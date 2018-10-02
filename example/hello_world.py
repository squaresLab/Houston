#!/usr/bin/env python3
import copy
import json
import logging

import bugzoo
from bugzoo import BugZoo

import houston
from houston.command import Command
from houston.environment import Environment
from houston.generator.rand import RandomTestGenerator
from houston.generator.resources import ResourceLimits
from houston.test import Test
from houston.runner import TestRunnerPool
#from houston.ardu.common.goto import CircleBasedGotoGenerator
from houston.root_cause.delta_debugging import DeltaDebugging
from houston.root_cause.symex import SymbolicExecution
import copy
from houston.ardu.copter.state import State as CopterState
from houston.ardu.rover.state import State as RoverState
from houston.ardu.configuration import Configuration as ArduConfig


from houston.ardu.copter import Takeoff, GoTo, ArmDisarm, SetMode


def setup_logging() -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG)
    logging.getLogger('houston').addHandler(log_to_stdout)


def run_single_test(sandbox, test):
    res = sandbox.run(test)
    print(res)

def run_single_test_with_coverage(sandbox, test):
    (res, coverage) = sandbox.run_with_coverage(test)
    print("Done")
    print(coverage)

### Run all tests stored to a json file
def run_all_tests(sut, test_file, coverage=False):
    tests = []
    with open(test_file, "r") as f:
        tests_json = json.load(f)
        tests = list(map(Test.from_json, tests_json))
    assert isinstance(tests, list)


    outcomes = {}
    coverages = {}
    def record_outcome(test, outcome, coverage=None):
        outcomes[test] = outcome
        coverages[test] = coverage

    runner_pool = TestRunnerPool(sut, 4, tests, record_outcome, coverage)
    print("Started running")
    runner_pool.run()
    print("Done running")
    print(outcomes)

    with open("example/failed.json", "w") as f:
        for m in outcomes:
            if not outcomes[m].passed:
                f.write(str(m.to_json()))
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
        with open("example/localization.json", "w") as f:
            f.write(str(l))

### Generate tests
def generate(sut, initial, environment, number_of_tests, max_num_actions=3):
    test_generator = RandomTestGenerator(sut, initial, environment, max_num_actions=max_num_actions, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_tests, 1000)
    tests = test_generator.generate(100, resource_limits)
    print("### {}".format(tests))
    with open("example/tests.json", "w") as f:
        test_descriptions = list(map(Test.to_json, tests))
        print(str(test_descriptions))
        json.dump(test_descriptions, f)


### Generate and run tests
def generate_and_run(sut, initial, environment, number_of_tests):
    test_generator = RandomTestGenerator(sut, initial, environment)
    resource_limits = ResourceLimits(number_of_tests, 1000)
    test_generator.generate_and_run(100, resource_limits)
    #test_generator.prepare(100, resource_limits)
    #for i in range(number_of_tests):
    #    m = test_generator.generate_test()
    #    print("Test {}: {}".format(i, m.to_json()))
    #    res = sandbox.run(m)
    print("DONE")


### Generate and run tests with mutation operator
def generate_and_run_mutation(sut, initial_state, environment, initial_test, number_of_tests):
    test_generator = MutationBasedTestGenerator(sut, initial, environment, initial_test, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_tests*5, 1000, number_of_tests)
    test_generator.generate_and_run(100, resource_limits, with_coverage=True)
    print("DONE")
    with open("example/tests-mutation.json", "w") as f:
        test_descriptions = list(map(Test.to_json, test_generator.history))
        print(str(test_descriptions))
        json.dump(test_descriptions, f)
        f.write("\n")
        test_descriptions = list(map(Test.to_json, test_generator.most_fit_tests))
        print(str(test_descriptions))
        json.dump(test_descriptions, f)



### Generate and run tests with fault localization
def generate_and_run_with_fl(sut, initial, environment, number_of_tests):
    test_generator = RandomTestGenerator(sut, initial, environment, max_num_actions=3, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_tests, 1000)
    report = test_generator.generate_and_run(100, resource_limits, with_coverage=True)
    print("DONE")
    print(report)
    print(test_generator.coverage)
    print(test_generator.report_fault_localization())
    with open("fl.json", "w") as f:
        f.write(str(test_generator.report_fault_localization()))


### Generate tests with symbolic execution
def generate_with_se(sut, initial, environment, config, test):
    se = SymbolicExecution(sut, initial, environment, config)
    tests = se.execute_symbolically(test)
    with open("example/tests.json", "w") as f:
        test_descriptions = list(map(Test.to_dict, tests))
        print(str(test_descriptions))
        json.dump(test_descriptions, f)


if __name__ == "__main__":
    setup_logging()
    bz = BugZoo()
    #snapshot = bz.bugs['ardubugs:010665f9']
    #snapshot = bz.bugs['afrl:AIS-Scenario1']
    snapshot = bz.bugs['afrl:overflow']

    config = ArduConfig(
        speedup=1,
        time_per_metre_travelled=5.0,
        constant_timeout_offset=1.0,
        min_parachute_alt=10.0)
    sut = houston.ardu.ArduCopter(snapshot, config)

    # test description
    cmds = [
        ArmDisarm(arm=False),
        ArmDisarm(arm=True),
        #SetMode(mode='GUIDED'),
        Takeoff(altitude=3.0),
        #GoTo(latitude=-35.361354, longitude=149.165218, altitude=5.0),
        SetMode(mode='LAND'),
        ArmDisarm(arm=False)
    ]

    environment = Environment({})
    initial = CopterState(
        home_latitude=-35.3632607,
        home_longitude=149.1652351,
        latitude=-35.3632607,
        longitude=149.1652351,
        altitude=0.0,
        armed=False,
        armable=True,
        mode="GUIDED",
        ekf_ok=True,
        yaw=0.0,
        roll=0.0,
        pitch=0.0,
        roll_channel=0.0,
        throttle_channel=0.0,
        heading=0.0,
        groundspeed=0.0,
        airspeed=0.0,
        vx=0.0,
        vy=0.0,
        vz=0.0,
        time_offset=0.0)
    test = Test(config, environment, initial, cmds)

    # create a container for the test execution
    sandbox = sut.provision(bz)
    try:
        run_single_test(sandbox, test)
        #run_single_test_with_coverage(sandbox, test)
        #generate(sut, initial, environment, 100, 10)
        #run_all_tests(sut, "example/tests.json", False)
        #generate_and_run_mutation(sut, initial, environment, test, 3)
        #generate_and_run_with_fl(sut, initial, environment, 5)
        #run_single_test_with_coverage(sandbox, test)

        #d = DeltaDebugging(sut, initial, environment, config, [test])
        #d.find_root_cause()


        #generate(sut, initial, environment, 100, 10)
        # run_all_tests(sut, "example/tests.json", False)
        #generate_and_run_with_fl(sut, initial, environment, 5)
        #run_single_test_with_coverage(sandbox, test)

        #generate_with_se(sut, initial, environment, config, test)

    finally:
#        pass
        sandbox.destroy()
