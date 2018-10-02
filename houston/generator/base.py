import random
import threading
import timeit

import bugzoo

from ..runner import TestRunnerPool
from ..system import System
from ..test import Test, TestSuite
from .resources import ResourceUsage, ResourceLimits
from .report import TestGeneratorReport


class TestGeneratorStream(object):
    def __init__(self, generator):
        self.__lock = threading.Lock()
        self.__generator = generator

    def __iter__(self):
        """
        Returns an iterator for lazily fetching tests from the generator
        attached to this stream.
        """
        return self

    def __next__(self):
        """
        Requests the next test from the test generator.
        """
        g = self.__generator
        self.__lock.acquire()
        try:
            g.tick()
            if g.exhausted():
                raise StopIteration
            test = self.__generator.generate_test()
            g.tick()
            g.resource_usage.num_tests += 1
            test_num = g.resource_usage.num_tests
            print('Generated test: {}'.format(test_num))  # FIXME
            return test
        finally:
            self.__lock.release()


class TestGenerator(object):
    def __init__(self,
                 system: System,
                 threads: int = 1,
                 action_generators=None,
                 max_num_actions: int = 10
                 ) -> None:
        assert isinstance(system, System)
        assert isinstance(threads, int)
        assert isinstance(max_num_actions, int)
        assert threads > 0
        assert max_num_actions > 0

        if not action_generators:
            action_generators = []

        self.__system = system
        self.__threads = threads
        self.__max_num_actions = max_num_actions

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__action_generators = {}
        for g in action_generators:
            name = g.schema_name
            assert name not in self.__action_generators
            self.__action_generators[name] = g

    @property
    def resource_limits(self):
        return self.__resource_limits

    @property
    def resource_usage(self):
        return self.__resource_usage

    @property
    def system(self):
        """
        The system under test.
        """
        return self.__system

    @property
    def max_num_actions(self):
        """
        The maximum number of actions that may be present in a test
        produced by this generator.
        """
        return self.__max_num_actions

    @property
    def history(self):
        return self.__history

    @property
    def outcomes(self):
        return self.__outcomes

    @property
    def failures(self):
        return self.__failures

    @property
    def coverage(self):
        return self.__coverage

    @property
    def threads(self):
        """
        The number of threads available to this generator.
        """
        return self.__threads

    @property
    def rng(self):
        """
        Returns the pseudorandom number generator used by this generator.
        """
        return self.__rng

    def action_generator(self, schema):
        """
        Retrieves any action generator that has been associated with a given
        schema, or None if no action generator has been provided for the
        given schema.
        """
        name = schema.name
        if name in self.__action_generators:
            return self.__action_generators[name]
        return None

    def exhausted(self):
        """
        Checks whether the resources available to this generator have been
        exhausted.
        """
        return self.__resource_limits.reached(self.__resource_usage)

    def outcome(self, test):
        """
        Returns the outcome for a previously-executed test.
        """
        return self.__outcomes[test]

    def end_state(self, test):
        """
        Returns the end state after executing a given test.
        """
        assert isinstance(test, Test)
        if test.is_empty():
            return test.initial_state
        outcome = self.__outcomes[test]
        return outcome.end_state

    def executed_path(self, m):
        """
        Returns the path that was taken when a given test was executed.
        """
        if m.is_empty():
            return BranchPath([])
        outcome = self.__outcomes[m]
        return outcome.executed_path

    def tick(self):
        """
        Used to measure the running time of the current generation trial.
        """
        self.__resource_usage.running_time = \
            timeit.default_timer() - self.__start_time

    def execute_test(self, test, container):
        """
        Executes a given test using a provided container.
        """
        print("executing test..."),
        outcome = container.execute(test)
        self.record_outcome(test, outcome)
        print("\t[DONE]")
        return outcome

    def record_outcome(self, test, outcome, coverage=None):
        """
        Records the outcome of a given test. The test is logged to the
        history, and its outcome is stored in the outcome dictionary. If the
        test failed, the test is also added to the set of failed
        tests.
        """
        self.__history.append(test)
        self.__outcomes[test] = outcome
        if coverage:
            self.__coverage[test] = coverage

        if outcome.failed:
            self.__failures.add(test)

    def generate(self, seed, resource_limits):
        """
        Generate tests and return them
        """
        assert isinstance(seed, int)

        tests = []
        self.prepare(seed, resource_limits)
        stream = TestGeneratorStream(self)
        try:
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()
            self.tick()
            # TODO use threads
            while True:
                test = stream.__next__()
                tests.append(test)
        except StopIteration:
            print("Done with generating tests")
        return tests

    def generate_and_run(self, seed, resource_limits, with_coverage=False):
        assert isinstance(seed, int)
        self.__runner_pool = None

        try:
            self.prepare(seed, resource_limits)
            stream = TestGeneratorStream(self)
            self.__runner_pool = TestRunnerPool(self.system,
                                                   self.threads,
                                                   stream,
                                                   self.record_outcome,
                                                   with_coverage)
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()
            self.tick()
            self.__runner_pool.run()

            # produce a test suite that best fits the desired
            # characteristics
            suite = self.reduce()

            # summarise the generation process
            report = TestGeneratorReport(self.system,
                                            self.history,
                                            self.outcomes,
                                            self.failures,
                                            self.resource_usage,
                                            self.resource_limits,
                                            self.coverage,
                                            suite)
            return report

        finally:
            if self.__runner_pool:
                self.__runner_pool.shutdown()
                self.__runner_pool = None

    def reduce(self):
        """
        """
        # TODO remove all failures from the history list
        return TestSuite(self.__history)

    def prepare(self, seed, resource_limits):
        """
        Prepares the state of this generator immediately before beginning a
        new generation trial.
        """
        self.__resource_limits = resource_limits
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self.__coverage = {}
        self.__rng = random.Random(seed)

    def generate_test(self):
        """
        Generates a single test according to the generation strategy defined
        by this generator.
        """
        raise NotImplementedError

    # FIXME what does this do? what does fault localization have to do with
    # test generation in general? feels like this is in the wrong place.
    def report_fault_localization(self):
        from bugzoo.core.coverage import TestSuiteCoverage
        from bugzoo.core.spectra import Spectra
        from bugzoo.localization import Localization
        from bugzoo.localization.suspiciousness import tarantula

        # FIXME why the need to build indirectly?
        test_suite_coverage_dict = {}
        counter = 0
        for m in self.coverage:
            test = {
                'test': 't{}'.format(counter),
                'outcome': self.outcome(m).to_test_outcome_json(0),
                'coverage': self.coverage[m].to_dict()
            }
            test_suite_coverage_dict['t{}'.format(counter)] = test
            counter += 1
        # FIXME why not build it directly?
        coverage = TestSuiteCoverage.from_dict(test_suite_coverage_dict)
        spectra = Spectra.from_coverage(coverage)
        loc = Localization.from_spectra(spectra, tarantula)

        return loc
