import os
import sys
import argparse
import logging

from compare_traces import load_file as load_trace_file

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)

DESCRIPTION = "Performs sanity checking of trace files"


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('trace', type=str, help='path to a trace file.')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity')
    return p.parse_args()


def main() -> None:
    args = parse_args()
    setup_logging(verbose=args.verbose)
    fn_trace = args.trace

    if not os.path.exists(fn_trace):
        logger.error("trace file not found: %s", fn_trace)
        sys.exit(1)

    logger.info("sanity checking trace file: %s", fn_trace)
    mission, traces = load_trace_file(fn_trace)

    logger.info("speedup factor: %dX", mission.configuration.speedup)
    logger.info("mission contains %d commands", len(mission.commands))
    logger.info('\n'.join([
        f' {i}. {cmd}' for i, cmd in enumerate(mission.commands)
    ]))

    logger.info("file contains %d traces for mission", len(traces))
    num_execs = [len(t.commands) for t in traces]
    logger.info("number of commands executed by each trace:\n%s",
                '\n'.join([f" {i}. {n} commands executed"
                           for i, n in enumerate(num_execs)]))


if __name__ == '__main__':
    main()
