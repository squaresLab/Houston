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
from hash_mutants import mutation_to_uid
from verify_test_data import VerifiedEntry, NewDatabaseEntry, Status
from filter_truth import VALID_LIST_OUTPUT

from enum import Enum

logger = logging.getLogger("houston")  # type: logging.Logger
logger.setLevel(logging.DEBUG)


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Validate test traces')
    parser.add_argument('database', type=str, action='store',
                       help='path to test database yaml file.')
    parser.add_argument('daikon_out', type=str, action='store',
                        help='path to the output invariant checker')
    parser.add_argument('nonce_file', type=str, action='store',
                        help='path to nonce file.')
    parser.add_argument('ground_truth', type=str, action='store',
                        help='path to ground truth traces')
#    parser.add_argument('output', action='store', type=str,
#                        help='the file where the results will be stored')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')
    parser.add_argument('--compute-score', action='store',
                        default='',
                        help='path to a csv file to add the accuracy results')
    args = parser.parse_args()
    return args


def compute_score(entries: List[NewDatabaseEntry],
                  score_file: str = '',
                  models_dir: str = '') -> None:
    tp, fp, tn, fn = 0, 0, 0, 0
    for o, t in entries:
        if Status.REJECTED in o.verified:
            fp += 1
        else:
            tn += 1
        if Status.REJECTED in t.verified:
            tp += 1
        else:
            fn += 1

    logger.info("TP: %d, TN: %d, FP: %d, FN: %d", tp, tn, fp, fn)
    precision = float(tp)/float(tp + fp) if tp+fp != 0 else float('nan')
    recall = float(tp)/float(tp + fn) if tp+fn != 0 else float('nan')
    f_score = (2 * tp) / (2 * tp + fp + fn) if (tp + fp + fn) else float('nan')
    logger.info("Precision: %f\nRecall: %f\nF-score: %f",
                precision, recall, f_score)
    if not score_file:
        return
    typ = 'daikon'
    seed = os.path.basename(os.path.dirname(models_dir))
    data_amount = os.path.basename(os.path.dirname(os.path.dirname(models_dir)))
    with open(score_file, 'a') as f:
        f.write(', '.join([data_amount, seed, typ, '-', str(tp), str(tn), str(fp), str(fn),
                           str(precision), str(recall), str(f_score)]))
        f.write('\n')


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    results = []

    with open(args.database, 'r') as f:
        db = YAML().load(f)

    with open(args.daikon_out, 'r') as f:
        invalidated = YAML().load(f)

    with open(args.nonce_file, 'r') as f:
        fn_to_nonce = YAML().load(f)

    with open(os.path.join(args.ground_truth, VALID_LIST_OUTPUT), 'r') as f:
        all_truth = YAML().load(f)
    all_truth = [os.path.join(args.ground_truth, t) for t in all_truth]


    entries = [DatabaseEntry.from_dict(e) for e in db['entries'] if e['inconsistent']]
    logger.info("starting with %d mutants", len(entries))


    traces = []
    for entry in entries:
        for _, trace_fn in entry.fn_inconsistent_traces:
            trace = VerifiedEntry(trace_fn,
                                [Status.REJECTED if n in invalidated else Status.ACCEPTED for n in fn_to_nonce[trace_fn]])
            traces.append(trace)
    oracles = []
    for oracle_fn in all_truth[:len(traces)]:
        oracle = VerifiedEntry(oracle_fn,
                               [Status.REJECTED if n in invalidated else Status.ACCEPTED for n in fn_to_nonce[oracle_fn]])
        oracles.append(oracle)
    validated_results = list(zip(oracles, traces))

    logger.debug("finished evaluating %d", len(validated_results))
    
    jsn = {
        'oracle-directory': db['oracle-directory'],
        'snapshot': db['snapshot'],
        'entries': [e.to_dict() for e in validated_results]
    }
    with open(args.output, 'w') as f:
        YAML().dump(jsn, f)
    logger.info("wrote results to file")
    if args.compute_score:
        compute_score(validated_results,
                      args.compute_score,
                      args.daikon_out)
    else:
        compute_score(validated_results)
