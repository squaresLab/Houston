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
    parser.add_argument('output', action='store', type=str,
                        help='the file where the results will be stored')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')

    args = parser.parse_args()
    return args


def compute_score(entries: List[NewDatabaseEntry]) -> None:
    tp, fp, tn, fn = 0, 0, 0, 0
    for e in entries:
        for o, t in e.fn_inconsistent_traces:
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
    recall = float(tp)/float(tp + tn) if tp+tn != 0 else float('nan')
    f_score = 2 * precision * recall / (precision + recall) if not (math.isnan(precision) or math.isnan(recall)) else float('nan')
    logger.info("Precision: %f\nRecall: %f\nF-score: %f",
                precision, recall, f_score)


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

    entries = [DatabaseEntry.from_dict(e) for e in db['entries'] if e['inconsistent']]
    logger.info("starting with %d mutants", len(entries))

    validated_results = []

    for entry in entries:
        pairs = []
        for oracle_fn, trace_fn in entry.fn_inconsistent_traces:
            oracle = VerifiedEntry(oracle_fn,
                                [Status.REJECTED if n in invalidated else Status.ACCEPTED for n in fn_to_nonce[oracle_fn]])
            trace = VerifiedEntry(trace_fn,
                                [Status.REJECTED if n in invalidated else Status.ACCEPTED for n in fn_to_nonce[trace_fn]])
            pairs.append((oracle, trace))
        validated_results.append(NewDatabaseEntry(entry.diff, tuple(pairs)))

    logger.debug("finished evaluating")
    
    jsn = {
        'oracle-directory': db['oracle-directory'],
        'snapshot': db['snapshot'],
        'entries': [e.to_dict() for e in validated_results]
    }
    with open(args.output, 'w') as f:
        YAML().dump(jsn, f)
    logger.info("wrote results to file")

    compute_score(validated_results)
