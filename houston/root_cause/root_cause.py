from typing import Set, Optional, Tuple, Dict, List, Any
import random

from ..system import System
from ..state import State
from ..environment import Environment
from ..test import Test, TestOutcome
from ..valueRange import DiscreteValueRange
from ..command import Command, Parameter
from ..configuration import Configuration

Domain = List[Tuple[int, Any, List[Parameter]]]


class TestDomain(object):
    """
    Specification of a range of tests.
    """
    def __init__(self, initial_domain: Domain = None) -> None:
        if not initial_domain:
            initial_domain = []
        self.__domain = initial_domain

    def __str__(self) -> str:
        return str(self.domain)

    @property
    def domain(self) -> Domain:
        """
        The domain specified by sequence of Actions with
        specific parameter ranges.
        """
        return self.__domain

    @staticmethod
    def from_initial_test(test: Test,
                          discrete_params: bool = False)\
            -> 'TestDomain':
        """
        Create a test domain by considering the initial sequence
        of actions in test and all possible values for parameters.
        """
        i = 0
        domain = []
        for command in test.commands:
            if discrete_params:
                parameters = [Parameter(p.name,
                                        DiscreteValueRange([command[p.name]]))
                              for p in command.parameters]
            else:
                parameters = command.parameters
            domain.append((i, command.__class__, parameters))
            i += 1
        return TestDomain(domain)

    @property
    def command_size(self) -> int:
        """
        Number of actions in this domain.
        """
        return len(self.__domain)

    def generate_test(self,
                      environment: Environment,
                      initial_state: State,
                      config: Configuration,
                      rng: random.Random
                      ) -> Test:
        """
        Return a test in this domain.
        """
        cmds = []
        for _, cmd_class, params in self.domain:
            parameters = {}
            for p in params:
                parameters[p.name] = p.generate(rng)
            cmds.append(cmd_class(**parameters))
        return Test(config, environment, initial_state, cmds)


class RootCauseFinder(object):
    """
    RootCauseFinder is used to find minimum requirements that
    results in test failure the same way that initial failing
    tests do.
    """
    def __init__(self,
                 system: System,
                 initial_state: State,
                 environment: Environment,
                 config: Configuration,
                 initial_failing_tests: List[Test],
                 random_seed: int = 100
                 ) -> None:

        assert(len(initial_failing_tests) > 0)

        self.__system = system
        self.__initial_state = initial_state
        self.__environment = environment
        self.__rng = random.Random(random_seed)
        self.__initial_failing_tests = initial_failing_tests
        self.__configuration = config

    @property
    def system(self) -> System:
        """
        The system under test.
        """
        return self.__system

    @property
    def initial_state(self) -> State:
        """
        the initial state used for running all tests.
        """
        return self.__initial_state

    @property
    def environment(self) -> Environment:
        """
        the environment used for running all tests.
        """
        return self.__environment

    @property
    def initial_failing_tests(self) -> Test:
        """
        the failing tests provided by the user.
        """
        return self.__initial_failing_tests

    @property
    def configuration(self) -> Configuration:
        return self.__configuration

    @property
    def rng(self) -> random.Random:
        return self.__rng

    def find_root_cause(self, time_limit: float = 0.0) -> TestDomain:
        """
        The main function that finds the root cause.
        """
        raise NotImplementedError
