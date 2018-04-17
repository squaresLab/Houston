from typing import Set, Optional, Tuple, Dict, List


from houston.system import System
from houston.state import State
from houston.mission import Mission, MissionOutcome


class MissionDomain(object):
    """
    Specification of a range of missions.
    """
    def __init__(self, system: System, initial_domain=[]):
        self.__system = system
        self.__domain = initial_domain


    @property
    def domain(self): -> List[Tuple[str, List[Parameter]]]
        """
        The domain specified by sequence of Actions with
        specific parameter ranges.
        """
        return self.__domain


    @staticmethod
    def from_initial_mission(system: System, mission: Mission):
        """
        Create a mission domain by considering the initial sequence
        of actions in mission and all possible values for parameters.
        """
        domain = []
        for action in mission.actions:
            parameters = system.schemas[action.schema_name].parameters
            domain.append((action.schema_name, parameters))
        return MissionDomain(system, domain)


class RootCauseFinder(object):
    """
    RootCauseFinder is used to find minimum requirements that
    results in mission failure the same way that initial failing
    missions do. 
    """
    def __init__(self, system: System, initial_state: State, initial_failing_missions: List[Mission]):
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

