from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import argparse
import logging
import sys
import os

from ruamel.yaml import YAML
import yaml
from houston.mission import Mission

from compare_traces import load_file as load_traces_file
from compare_traces import is_truth_valid

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)

DESCRIPTION = "Filter out ground truth data."

VALID_LIST_OUTPUT = "valid_list.yml"


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('oracle', type=str, help='path to oracle trace directory.')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity')
    return p.parse_args()


def filter_truth_traces(dir_oracle: str) -> List[str]:
    trace_filenames = \
        [fn for fn in os.listdir(dir_oracle) if fn.endswith('.json')]
    valid_traces = []
    for fn in trace_filenames:
        fn_trace = os.path.join(dir_oracle, fn)
        mission, oracle_traces = load_traces_file(fn_trace)
        oracle_traces = [t for t in oracle_traces if t.commands]
        if is_truth_valid(oracle_traces):
            valid_traces.append(fn)
        else:
            logger.debug("trace %s is invalid", fn)
    return valid_traces


def main():
    args = parse_args()
    setup_logging(verbose=args.verbose)
    dir_oracle = args.oracle

    if not os.path.exists(dir_oracle):
        logger.error("oracle directory not found: %s", dir_oracle)
        sys.exit(1)

    # obtain a list of oracle traces
    trace_filenames = filter_truth_traces(dir_oracle)
    logger.info("Total number of %d valid truth", len(trace_filenames))

    with open(os.path.join(dir_oracle, VALID_LIST_OUTPUT), "w") as f:
        YAML().dump(trace_filenames, f)

if __name__ == '__main__':
    main()
