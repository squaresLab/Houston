from typing import Set, Optional, Tuple, Dict, List

from houston.root_cause import RootCauseFinder, MissionDomain
from houston.system import System
from houston.state import State
from houston.mission import Mission



class DeltaDebugging(RootCauseFinder):
    """
    Conducts delta debugging on a failing mission to narrow
    it down to main problem.
    """
    def __init__(self, system: System, initial_state: State, initial_failing_missions: List[Mission]):
        self.__domain = MissionDomain.from_initial_mission(system, initial_failing_missions[0], discrete_params=True)

        super(DeltaDebugging, self).__init__(system, initial_state, initial_failing_missions)


    @property
    def domain(self):
        """
        The domain where the failure happens.
        """
        return self.__domain


    def find_root_cause(self, time_limit=None) -> MissionDomain:
        empty_domain = MissionDomain(self.system)
        return self._dd2(self.domain, empty_domain)


    def _dd2(self, c: MissionDomain, r: MissionDomain) -> MissionDomain:

        if c.action_size == 1:
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

        final_domain = DeltaDebugging._union(self._dd2(c1, m2), self._dd2(c2, m1))
        return final_domain


    def _run(self, mission):
        """
        runs a mission using sandbox and returns whether the mission passed.
        """
        sandbox = self.system.provision()
        res = sandbox.run(mission)
        sandbox.destroy()

        return res.passed


    @staticmethod
    def _divide(c: MissionDomain):
        """
        Divides a domain into two almost equal domains.
        """
        mid = int(c.action_size/2)
        c1 = MissionDomain(c.system, c.domain[:mid])
        c2 = MissionDomain(c.system, c.domain[mid:])
        return c1, c2


    @staticmethod
    def _union(c1: MissionDomain, c2: MissionDomain) -> MissionDomain:
        """
        Returns the union of two domains.
        """
        action_list = []
        i1 , i2 = 0, 0
        while i1 < c1.action_size or i2 < c2.action_size:
            if i1 >= c1.action_size or (i2 < c2.action_size and c2.domain[i2][0] < c1.domain[i1][0]):
                action_list.append(c2.domain[i2])
                i2 += 1
            else:
                action_list.append(c1.domain[i1])
                i1 += 1
        c = MissionDomain(c1.system, action_list)
        return c



