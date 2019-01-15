#!/usr/bin/env python3
import copy
import json
import logging

import argparse
import bugzoo
from bugzoo import BugZoo

import houston
from houston.command import Command
from houston.environment import Environment
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits
from houston.mission import Mission
from houston.runner import MissionRunnerPool
#from houston.ardu.common.goto import CircleBasedGotoGenerator
from houston.root_cause.delta_debugging import DeltaDebugging
from houston.root_cause.symex import SymbolicExecution
import copy
from houston.ardu.copter.state import State as CopterState
from houston.ardu.rover.state import State as RoverState
from houston.ardu.configuration import Configuration as ArduConfig


from houston.ardu.copter import Takeoff, GoTo, ArmDisarm, SetMode
from settings import sut


def setup_logging() -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG)
    logging.getLogger('houston').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Running something.')
    parser.add_argument('snapshot', type=str,
                        help='name of the snapshot to be used.')
    parser.add_argument('--input_file', default="missions.json", type=str,
                        help='path to json file containing the missions')
    parser.add_argument('--coverage', default=False, action="store_true",
                        help='if given fault localization will be done at the end.')
    parser.add_argument('--not_record', default=True, action="store_false",
                        help='if given the results will not be recorded.')
    parser.add_argument('--threads', default=5,
                        help='number of threads to be used for this run.')
    args = parser.parse_args()
    return args


def run_single_mission(sandbox, mission):
    res = sandbox.run(mission)
    print(res)

def run_single_mission_with_coverage(sandbox, mission):
    (res, coverage) = sandbox.run_with_coverage(mission)
    print("Done")
    print(coverage)

### Run all missions stored in a JSON file
def run_all_missions(bz, snapshot_name, sut, mission_file, coverage=False, record=True, threads=5):
    missions = []
    with open(mission_file, "r") as f:
        missions_json = json.load(f)
        missions = list(map(Mission.from_dict, missions_json))
    assert isinstance(missions, list)


    outcomes = {}
    coverages = {}
    def record_outcome(mission, outcome, coverage=None):
        outcomes[mission] = outcome
        coverages[mission] = coverage

    runner_pool = MissionRunnerPool(bz, snapshot_name, sut, threads, missions, record_outcome, coverage, record)
    print("Started running")
    runner_pool.run()
    print("Done running")
    print(outcomes)

    with open("failed.json", "w") as f:
        for m in outcomes:
            if not outcomes[m].passed:
                f.write(str(m.to_dict()))
                f.write("\n")

    if coverage:
        from bugzoo.core.coverage import TestSuiteCoverage
        from bugzoo.core.spectra import Spectra
        from bugzoo.localization import Localization
        from bugzoo.localization.suspiciousness import tarantula
        test_suite_coverage_dict = {}
        counter = 0
        for m in coverages:
            test = {
                    'test': 't{}'.format(counter),
                    'outcome': outcomes[m].to_test_outcome_json(0),
                    'coverage': coverages[m].to_dict()
            }
            test_suite_coverage_dict['t{}'.format(counter)] = test
            counter += 1
        spectra = Spectra.from_coverage(TestSuiteCoverage.from_dict(test_suite_coverage_dict))
        l = Localization.from_spectra(spectra, tarantula)
        print(str(l.get_most_suspicious_lines()))
        with open("localization.json", "w") as f:
            f.write(str(l))


if __name__ == "__main__":
    setup_logging()
    args = setup_arg_parser()
    bz = BugZoo()

    run_all_missions(bz, args.snapshot, sut, args.input_file, args.coverage,
                     args.not_record, args.threads)
