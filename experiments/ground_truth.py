from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import concurrent.futures
import argparse
import functools
import contextlib
import attr
import logging
import json
import sys
import os

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import PreservedScalarString
import yaml
import bugzoo
import boggart
import rooibos
import houston
from bugzoo import BugZoo as BugZooDaemon
from houston import System
from houston.mission import Mission
from houston.trace import CommandTrace, MissionTrace
from houston.ardu.copter import ArduCopter

from compare_traces import load_file as load_traces_file
from compare_traces import matches_ground_truth

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)

DESCRIPTION = "Builds a ground truth dataset."


@attr.s
class DatabaseEntry(object):
    diff = attr.ib(type=str)
    fn_oracle = attr.ib(type=str)
    fn_trace = attr.ib(type=str)

    def to_dict(self) -> Dict[str, Any]:
        return {'diff': PreservedScalarString(self.diff),
                'oracle': self.fn_oracle,
                'trace': self.fn_trace}


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('snapshot', help='the name of the BugZoo snapshot')
    p.add_argument('mutants', help='path to a JSON file of mutants.')
    p.add_argument('oracle', type=str, help='path to oracle trace directory.')
    p.add_argument('output', type=str,
                   help='the file to which the ground truth dataset should be written.')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity')
    p.add_argument('--threads', type=int, default=1,
                   help='number of threads to use when building trace files.')
    return p.parse_args()


def process_mutation(system: Type[System],
                     daemon_bugzoo: BugZooDaemon,
                     snapshot: bugzoo.Bug,
                     trace_filenames: List[str],
                     dir_mutant_traces: str,
                     diff: str
                     ) -> Optional[DatabaseEntry]:
    patch = bugzoo.Patch.from_unidiff(diff)
    bz = daemon_bugzoo
    sandbox_cls = system.sandbox
    container = None  # type: Optional[bugzoo.Container]
    try:
        container = bz.containers.provision(snapshot)
        logger.debug("built container")
        if not bz.containers.patch(container, patch):
            logger.error("failed to patch using diff: %s", diff)
            return None
        if not bz.containers.build(container).successful:
            logger.error("failed to build mutant: %s", diff)
            return None

        def obtain_trace(mission: houston.Mission) -> MissionTrace:
            args = [bz, container, mission.initial_state,
                    mission.environment, mission.configuration]
            with sandbox_cls.for_container(*args) as sandbox:
                return sandbox.run_and_trace(mission.commands)

        for fn_trace in trace_filenames:
            logger.debug("evaluating oracle trace: %s", fn_trace)
            mission, oracle_traces = load_traces_file(fn_trace)
            trace_mutant = obtain_trace(mission)

            if not matches_ground_truth(trace_mutant, oracle_traces):
                logger.info("found an acceptable mutant!")

                # write mutant trace to file
                identifier = abs(hash((hash(diff), hash(mission))))
                fn_trace_mut_rel = "{}.json".format(identifier)
                fn_trace_mut = os.path.join(dir_mutant_traces, fn_trace_mut_rel)
                jsn = {'mission': mission.to_dict(),
                       'traces': [trace_mutant.to_dict()]}
                with open(fn_trace_mut, 'w') as f:
                    json.dump(jsn, f)

                entry = DatabaseEntry(diff, fn_trace, fn_trace_mut)
                return entry
            else:
                logger.debug("mutant is not sufficiently different for given mission.")

    except Exception:
        logger.exception("failed to obtain data for mutant: %s", diff)
        return None
    except (houston.exceptions.NoConnectionError, houston.exceptions.ConnectionLostError):
        logger.error("mutant resulted in crash")
        return None
    finally:
        del bz.containers[container.id]
    return None


def main():
    args = parse_args()
    setup_logging(verbose=args.verbose)
    name_snapshot = args.snapshot
    fn_mutants = args.mutants
    dir_output = args.output
    dir_oracle = args.oracle
    fn_output_database = os.path.join(dir_output, 'database.yml')
    num_threads = args.threads
    system = ArduCopter

    assert num_threads >= 1

    # ensure that the output directory exists
    os.makedirs(args.output, exist_ok=True)

    if not os.path.exists(dir_oracle):
        logger.error("oracle directory not found: %s", dir_oracle)
        sys.exit(1)

    # load the mutant diffs
    try:
        with open(fn_mutants, 'r') as f:
            diffs = [e['diff'] for e in yaml.load(f)]
            logger.debug("loaded %d diffs from database", len(diffs))
    except Exception:
        logger.exception("failed to load mutation database: %s", fn_mutants)
        sys.exit(1)
    except FileNotFoundError:
        logger.error("mutation database file not found: %s", fn_mutants)
        sys.exit(1)

    # obtain a list of oracle traces
    trace_filenames = \
        [fn for fn in os.listdir(dir_oracle) if fn.endswith('.json')]
    trace_filenames = [os.path.join(dir_oracle, fn) for fn in trace_filenames]

    db_entries = []  # type: List[DatabaseEntry]
    futures = []
    with bugzoo.server.ephemeral() as client_bugzoo:
        with concurrent.futures.ProcessPoolExecutor(max_workers=num_threads) as executor:
            snapshot = client_bugzoo.bugs[name_snapshot]
            process = functools.partial(process_mutation,
                                        system,
                                        client_bugzoo,
                                        snapshot,
                                        trace_filenames,
                                        dir_output)
            for diff in diffs:
                future = executor.submit(process, diff)
                futures.append(future)

        for future in concurrent.futures.as_completed(futures):
            entry = future.result()
            db_entries.append(entry)

    # save to disk
    logger.info("finished constructing evaluation dataset.")
    logger.debug("saving evaluation dataset to disk.")
    jsn = {
        'oracle-directory': dir_oracle,
        'snapshot': name_snapshot,
        'entries': [e.to_dict() for e in db_entries if e]
    }
    with open(fn_output_database, 'w') as f:
        YAML().dump(jsn, f)
    logger.info("saved evaluation dataset to disk")


if __name__ == '__main__':
    main()
