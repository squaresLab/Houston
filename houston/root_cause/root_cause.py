from typing import Set, Optional, Tuple, Dict, List


from houston.system import System
from houston.state import State
from houston.mission import Mission, MissionOutcome
from houston.action import Parameter
from houston.valueRange import DiscreteValueRange


class MissionDomain(object):
    """
    Specification of a range of missions.
    """
    def __init__(self, system: System, initial_domain=[]):
        self.__system = system
        self.__domain = initial_domain


    def __str__(self):
        return str(self.domain)


    @property
    def system(self):
        """
        The system under which this domain is defined.
        """
        return self.__system


    @property
    def domain(self): -> List[Tuple[int, str, List[Parameter]]]
        """
        The domain specified by sequence of Actions with
        specific parameter ranges.
        """
        return self.__domain


    @staticmethod
    def from_initial_mission(system: System, mission: Mission, discrete_params=False):
        """
        Create a mission domain by considering the initial sequence
        of actions in mission and all possible values for parameters.
        """
        i = 0
        for action in mission.actions:
            if discrete_params:
                parameters = [Parameter(v, DiscreteValueRange([action.values[v]])) for v in action.values]
            else:
                parameters = system.schemas[action.schema_name].parameters
            domain.append((i, action.schema_name, parameters))
            i += 1
        return MissionDomain(system, domain)


    @property
    def action_size(self):
        """
        Number of actions in this domain.
        """
        return len(self.__domain)


class RootCauseFinder(object):
    """
    RootCauseFinder is used to find minimum requirements that
    results in mission failure the same way that initial failing
    missions do. 
    """
    def __init__(self, system: System, initial_state: State, initial_failing_missions: List[Mission]):
        assert(len(initial_failing_missions) > 0)

        self.__system = system
        self.__initial_state = initial_state
        self.__initial_failing_missions = initial_failing_missions


    @property
    def system(self):
        """
        The system under test.
        """
        return self.__system


    @property
    def initial_state(self):
        """
        The initial state used for running all missions.
        """
        return self.__initial_state


    @property
    def initial_failing_missions(self):
        """
        The failing missions provided by the user.
        """
        return self.__initial_failing_missions


    def find_root_cause(self, time_limit=None): -> MissionDomain
        """
        The main function that finds the root cause.
        """
        raise NotImplementedError

