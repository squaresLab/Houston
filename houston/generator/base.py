import random
import threading
import timeit
from bugzoo.client import Client as BugZooClient

import logging
from typing import Dict, Callable, List, Type, Optional

from ..runner import MissionRunnerPool
from ..system import System
from ..mission import Mission, MissionSuite, MissionOutcome
from ..command import Command
from .resources import ResourceUsage, ResourceLimits
from .report import MissionGeneratorReport

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class MissionGeneratorStream(object):
    def __init__(self, generator):
        self.__lock = threading.Lock()
        self.__generator = generator

    def __iter__(self):
        """
        Returns an iterator for lazily fetching missions from the generator
        attached to this stream.
        """
        return self

    def __next__(self):
        """
        Requests the next mission from the mission generator.
        """
        g = self.__generator
        with self.__lock:
            g.tick()
            if g.exhausted():
                raise StopIteration
            mission = self.__generator.generate_mission()
            g.tick()
            g.resource_usage.num_missions += 1
            mission_num = g.resource_usage.num_missions
            logger.debug('Generated mission: %d', mission_num)
            return mission


class MissionGenerator(object):
    def __init__(self,
                 system: Type[System],
                 threads: int = 1,
                 command_generators: Optional[Dict[str, Callable]] = None,
                 max_num_commands: int = 10
                 ) -> None:
        assert issubclass(system, System)
        assert isinstance(threads, int)
        assert isinstance(max_num_commands, int)
        assert threads > 0
        assert max_num_commands > 0

        if not command_generators:
            command_generators = {}

        self.__system = system
        self.__threads = threads
        self.__max_num_commands = max_num_commands

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__command_generators = command_generators

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
    def max_num_commands(self):
        """
        The maximum number of commands that may be present in a mission
        produced by this generator.
        """
        return self.__max_num_commands

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

    def command_generator(self, command: Type[Command]):
        """
        Retrieves any command generator that has been associated with a given
        schema, or None if no action generator has been provided for the
        given schema.
        """
        name = command.name
        if name in self.__command_generators:
            return self.__command_generators[name]
        return None

    def exhausted(self):
        """
        Checks whether the resources available to this generator have been
        exhausted.
        """
        return self.__resource_limits.reached(self.__resource_usage)

    def outcome(self, mission):
        """
        Returns the outcome for a previously-executed mission.
        """
        return self.__outcomes[mission]

    def end_state(self, mission):
        """
        Returns the end state after executing a given mission.
        """
        assert isinstance(mission, Mission)
        if mission.is_empty():
            return mission.initial_state
        outcome = self.__outcomes[mission]
        return outcome.end_state

    def executed_path(self, m):
        """
        Returns the path that was taken when a given mission was executed.
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

    def execute_mission(self,
                        bz: BugZooClient,
                        snapshot_name: str,
                        mission: Mission
                        ) -> MissionOutcome:
        """
        Executes a given mission using a provided container.
        """
        logger.info("executing mission..."),
        outcome = mission.run(self.bz, snapshot_name)
        self.record_outcome(mission, outcome)
        logger.ingo("\t[DONE]")
        return outcome

    def record_outcome(self, mission, outcome, coverage=None):
        """
        Records the outcome of a given mission. The mission is logged to the
        history, and its outcome is stored in the outcome dictionary. If the
        mission failed, the mission is also added to the set of failed
        missions.
        """
        self.__history.append(mission)
        self.__outcomes[mission] = outcome
        if coverage:
            self.__coverage[mission] = coverage

        if outcome.failed:
            self.__failures.add(mission)

    def generate(self,
                 seed: int,
                 resource_limits: ResourceLimits
                 ) -> List[Mission]:
        """
        Generate missions and return them
        """
        missions = []
        self.prepare(seed, resource_limits)
        stream = MissionGeneratorStream(self)
        try:
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()
            self.tick()
            # TODO use threads
            while True:
                mission = stream.__next__()
                missions.append(mission)
        except StopIteration:
            logger.info("Done with generating missions")
        return missions

    def generate_and_run(self,
                         seed: int,
                         resource_limits: ResourceLimits,
                         bz: BugZooClient,
                         snapshot: str,
                         with_coverage: bool = False
                         ) -> MissionGeneratorReport:
        self.__runner_pool = None

        try:
            self.prepare(seed, resource_limits)
            stream = MissionGeneratorStream(self)
            self.__runner_pool = MissionRunnerPool(bz,
                                                   snapshot,
                                                   self.system,
                                                   self.threads,
                                                   stream,
                                                   self.record_outcome,
                                                   with_coverage)
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()
            self.tick()
            self.__runner_pool.run()

            # produce a mission suite that best fits the desired
            # characteristics
            suite = self.reduce()

            # summarise the generation process
            report = MissionGeneratorReport(self.system,
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
        return MissionSuite(self.__history)

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

    def generate_mission(self):
        """
        Generates a single mission according to the generation strategy defined
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
