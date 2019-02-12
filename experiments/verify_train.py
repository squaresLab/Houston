from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import logging
import subprocess
import pexpect
import tempfile
import os
import json
import csv
import attr
import functools
import time
import math

import argparse
import concurrent.futures

from ruamel.yaml import YAML

from ground_truth import DatabaseEntry
from compare_traces import load_file
from filter_truth import VALID_LIST_OUTPUT
from hash_mutants import mutation_to_uid
from verify_test_data import VerifiedEntry, Status,\
    parse_data, check_against_model, reduce_dimension

from enum import Enum

logger = logging.getLogger("houston")  # type: logging.Logger
logger.setLevel(logging.DEBUG)


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)


@attr.s
class NewDatabaseEntry(object):
    diff = attr.ib(type=str)
    fn_inconsistent_traces = attr.ib(type=Tuple[Tuple[VerifiedEntry, VerifiedEntry], ...])

    def to_dict(self):
        return {'diff': self.diff,
                'uid': mutation_to_uid(self.diff),
                'inconsistent': [{'oracle': o.to_dict(), 'trace': {}} for o, t in self.fn_inconsistent_traces]}


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Validate test traces')
    parser.add_argument('train', type=str, action='store',
                       help='path to train directory.')
    parser.add_argument('models_dir', type=str, action='store',
                        help='path to directory with learned models.')
    parser.add_argument('GBDTs_path', type=str, action='store',
                        help='path to GBDTs.')
    parser.add_argument('--threshold', type=float, action='store',
                        default=0.4,
                        help='threshold for accepting a trace')
    parser.add_argument('--ignore-cat', action='store_true',
                        default=False,
                        help='ignore categorical fields of the data.')
    parser.add_argument('--separate-params', action='store_true',
                        default=False,
                        help='put parameters in a separate file')
    parser.add_argument('output', action='store', type=str,
                        help='the file where the results will be stored')
    parser.add_argument('--threads', type=int, default=1,
                         help='number of threads')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')

    args = parser.parse_args()
    return args


def verify_entry(oracle_fn,
                 model_checking) -> NewDatabaseEntry:
    all_data = []
    with open(oracle_fn, 'r') as f:
        gt_data = json.load(f)
    all_data.append({'mu': [],
                    'gt': [t for t in gt_data['traces'] if t['commands']]})

    logger.info("Len all_data: %d", len(all_data))
    cmd_based_dict, result = parse_data(all_data)
    logger.debug(cmd_based_dict)
    res = model_checking(all_data,
                         cmd_based_dict,
                         result)
    assert len(res) == len(all_data)
    logger.info("Final: {}".format(res))

    pairs = []
    for i in range(len(res)):
        oracle = VerifiedEntry(oracle_fn,
                               reduce_dimension(res[i]['gt']))
        pairs.append((oracle, None))
    return NewDatabaseEntry("", tuple(pairs))


def compute_score(entries: List[NewDatabaseEntry]) -> None:
    tp, fp, tn, fn = 0, 0, 0, 0
    for e in entries:
        for o, t in e.fn_inconsistent_traces:
            if Status.REJECTED in o.verified:
                fp += 1
            else:
                tn += 1

    logger.info("TP: %d, TN: %d, FP: %d, FN: %d", tp, tn, fp, fn)
    precision = float(tp)/float(tp + fp) if tp+fp != 0 else float('nan')
    recall = float(tp)/float(tp + tn) if tp+tn != 0 else float('nan')
    f_score = 2 * precision * recall / (precision + recall) if not (math.isnan(precision) or math.isnan(recall)) else float('nan')
    logger.info("Precision: %f\nRecall: %f\nF-score: %f",
                precision, recall, f_score)


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    results = []
    
    train_dir = args.train
    filtered_traces_fn = os.path.join(train_dir, VALID_LIST_OUTPUT)
    if os.path.exists(filtered_traces_fn):
        with open(filtered_traces_fn, 'r') as f:
            trace_filenames = YAML().load(f)
    else:
        raise Exception("VALID list not provided")
    trace_filenames = [os.path.join(train_dir, fn) for fn in trace_filenames]
    logger.info("Total number of %d valid truth", len(trace_filenames))

    validated_results = []
    futures = []
    model_checking = functools.partial(check_against_model,
                                       models_dir=args.models_dir,
                                       GBDTs_path=args.GBDTs_path,
                                       ignore_cat=args.ignore_cat,
                                       separate_params=args.separate_params,
                                       threshold=args.threshold)

    with concurrent.futures.ProcessPoolExecutor(args.threads) as e:
        for i, c in enumerate(trace_filenames):
            future = e.submit(verify_entry, c, model_checking)
            futures.append(future)

        logger.debug("submitted all candidates")
        for future in concurrent.futures.as_completed(futures):
            res = future.result()
            if res:
                validated_results.append(res)
        logger.debug("finished executing evaluating all mutants")
    
    jsn = {
        'entries': [e.to_dict() for e in validated_results]
    }
    with open(args.output, 'w') as f:
        YAML().dump(jsn, f)
    logger.info("wrote results to file")

    compute_score(validated_results)
