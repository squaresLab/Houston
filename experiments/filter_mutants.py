#!/usr/bin/env python3
__all__ = ['filter_mutants']

from typing import Tuple, List, Tuple, Set, Type
import argparse
import logging
import json
import os
import sys
import numpy as np
import concurrent.futures

from ruamel.yaml import YAML

from ground_truth import DatabaseEntry
from compare_traces import load_file, obtain_var_names,\
    simplify_trace, traces_contain_same_commands, SYSTEM

DESCRIPTION = """
The script to create an ordered list of suspicious mutants.
""".strip()

logger = logging.getLogger("houston")  # type: logging.Logger
logger.setLevel(logging.DEBUG)


def filter_mutants(
        candidate_mutant: DatabaseEntry,
        tolerance_factor: float,
        index: int
        ) -> List[Tuple[DatabaseEntry, float]]:

    logger.info("starting evaluation of candidate %d", index)
    useful_inconsistent_traces = []
    useless_inconsistent_traces = []
    for truth_fn, candidate_fn in candidate_mutant.fn_inconsistent_traces:
        _, truth = load_file(truth_fn)
        _, candidate = load_file(candidate_fn)
        candidate = candidate[0]

        truth = [t for t in truth if t.commands]

        # determine the sets of categorical and continuous variables
        state_cls = truth[0].commands[0].states[0].__class__
        categorical, continuous = obtain_var_names(state_cls)

        simple_candidate = simplify_trace(candidate)
        simple_truth = [simplify_trace(t) for t in truth]

        # check if the candidate trace executes a different sequence of commands
        # to the ground truth
        if not traces_contain_same_commands([candidate, truth[0]]):
            logger.debug("candidate trace doesn't have same commands as the truth")
            useless_inconsistent_traces.append((truth_fn, candidate_fn))
            continue

        # use the ground truth to build a distribution of expected values for
        # each continuous variable after the completion of each command
        num_commands = len(truth[0].commands)
        size_truth = len(truth)
        all_vars = SYSTEM.state.variables
        broken = False
        for i in range(num_commands):
            for var in continuous:
                vals = np.array([float(simple_truth[j][i][var])
                                for j in range(size_truth)])
                actual = simple_candidate[i][var]
                mid = max(vals) - ((max(vals) - min(vals)) / 2)
        #       tolerance = (max(vals) - min(vals)) / 2
        #       tolerance *= tolerance_factor
                tolerance = (all_vars[var].noise or 0.0) * tolerance_factor
                diff = abs(mid - actual)
                is_nearly_eq = np.isclose(mid, actual,
                                    rtol=1e-05, atol=tolerance, equal_nan=False)
                # logger.debug("%d:%s (%.9f +/-%.9f)", i, var, mid, tolerance)
                logger.debug("parameter [%s]: |%f - %f| = %f",
                                 var, mid, actual, diff)
                if not is_nearly_eq:
                    logger.debug("difference for parameter [%s] exceeds threshold (+/-%f)",
                                     var, all_vars[var].noise)
                    useful_inconsistent_traces.append((truth_fn, candidate_fn, diff/tolerance))
                    broken = True
                    break
            if broken:
                break
        if not broken:
            useless_inconsistent_traces.append((truth_fn, candidate_fn))
    if useful_inconsistent_traces:
        useless_inconsistent_traces.extend(list(candidate_mutant.fn_consistent_traces))
        max_diff = max(useful_inconsistent_traces, key=lambda k: k[2])[2]
        logger.debug('max_diff %f', max_diff)
        logger.info("finished evaluating candidate %d", index)
        return DatabaseEntry(candidate_mutant.diff,
                            tuple([(o, t) for o, t, _ in useful_inconsistent_traces]),
                            tuple(useless_inconsistent_traces)), max_diff
    logger.info("candidate %d isn't valid anymore", index)
    return None, 0.0


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('database', type=str, help='path to a database yaml file.')
    p.add_argument('output', type=str, help='path to output database yaml file.')
    p.add_argument('--top-n', type=int, default=0,
                   help='return top n most suspicious mutants.')
    p.add_argument('--threads', type=int, default=1,
                   help='number of threads')
    p.add_argument('--tolerance-factor', type=float, default=1.0,
                   help='tolerance factor')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity.')
    return p.parse_args()


def main():
    args = parse_args()
    setup_logging(args.verbose)

    assert args.top_n >= 0

    with open(args.database, 'r') as f:
        db = YAML().load(f)

    candidate_mutants = [DatabaseEntry.from_dict(e) for e in db['entries'] if e['inconsistent']]
    logger.info("starting with %d mutants", len(candidate_mutants))

    filtered_mutants = []
    futures = []
    with concurrent.futures.ProcessPoolExecutor(args.threads) as e:
        for i, c in enumerate(candidate_mutants):
            future = e.submit(filter_mutants, c, args.tolerance_factor, i)
            futures.append(future)

        logger.debug("submitted all candidates")
        for future in concurrent.futures.as_completed(futures):
            entry, max_diff = future.result()
            if entry:
                filtered_mutants.append((entry, max_diff))
        logger.debug("finished executing evaluating all mutants")

    logger.info("total number of valid mutants %d", len(filtered_mutants))
    filtered_mutants = sorted(filtered_mutants, key=lambda k: k[1], reverse=True)
    logger.debug("filtered_mutants %s", filtered_mutants)

    if args.top_n:
        filtered_mutants = filtered_mutants[:args.top_n]

    jsn = {
        'oracle-directory': db['oracle-directory'],
        'snapshot': db['snapshot'],
        'entries': [e.to_dict() for e, _ in filtered_mutants]
    }
    with open(args.output, 'w') as f:
        YAML().dump(jsn, f)


if __name__ == '__main__':
    main()
