from typing import Set, Optional, Tuple, Dict, List
from bugzoo import BugZoo

from .root_cause import RootCauseFinder, TestDomain
from ..system import System
from ..state import State
from ..environment import Environment
from ..test import Test
from ..configuration import Configuration


class DeltaDebugging(RootCauseFinder):
    """
    Conducts delta debugging on a failing test to narrow
    it down to main problem.
    """
    def __init__(self,
                 system: System,
                 initial_state: State,
                 environment: Environment,
                 config: Configuration,
                 initial_failing_tests: List[Test]
                 ) -> None:
        self.__domain = TestDomain.from_initial_test(
            initial_failing_tests[0], discrete_params=True)

        super(DeltaDebugging, self).__init__(system, initial_state,
                                             environment, config,
                                             initial_failing_tests)

    @property
    def domain(self) -> TestDomain:
        """
        The domain where the failure happens.
        """
        return self.__domain

    def find_root_cause(self, time_limit: float = 0.0) -> TestDomain:
        empty_domain = TestDomain()
        final_domain = self._dd2(self.domain, empty_domain)
        print("FINISHED: {}".format(str(final_domain)))

        return final_domain

    def _dd2(self, c: TestDomain, r: TestDomain) -> TestDomain:

        print("****** C: {}\n****** R: {}".format(str(c), str(r)))

        if c.command_size == 1:
            return c

        c1, c2 = DeltaDebugging._divide(c)

        m1 = DeltaDebugging._union(c1, r)
        res = self._run(m1)
        if not res:
            return self._dd2(c1, r)

        m2 = DeltaDebugging._union(c2, r)
        res = self._run(m2)
        if not res:
            return self._dd2(c2, r)

        final_domain = DeltaDebugging._union(self._dd2(c1, m2),
                                             self._dd2(c2, m1))
        return final_domain

    def _run(self, test_domain: TestDomain) -> bool:
        """
        runs a test using sandbox and returns whether the test passed.
        """
        test = test_domain.generate_test(self.environment,
                                         self.initial_state,
                                         self.configuration,
                                         self.rng)
        bz = BugZoo()
        sandbox = self.system.provision(bz)
        res = sandbox.run(test)
        sandbox.destroy()

        return res.passed

    @staticmethod
    def _divide(c: TestDomain) -> Tuple[TestDomain, TestDomain]:
        """
        Divides a domain into two almost equal domains.
        """
        mid = int(c.command_size / 2)
        c1 = TestDomain(c.domain[:mid])
        c2 = TestDomain(c.domain[mid:])
        return c1, c2

    @staticmethod
    def _union(c1: TestDomain, c2: TestDomain) -> TestDomain:
        """
        Returns the union of two domains.
        """
        command_list = []
        i1, i2 = 0, 0
        while i1 < c1.command_size or i2 < c2.command_size:
            if i1 >= c1.command_size or \
               (i2 < c2.command_size and c2.domain[i2][0] < c1.domain[i1][0]):
                command_list.append(c2.domain[i2])
                i2 += 1
            else:
                command_list.append(c1.domain[i1])
                i1 += 1
        c = TestDomain(command_list)
        return c
