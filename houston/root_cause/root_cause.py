from typing import Set, Optional, Tuple, Dict, List
import random

from ..system import System
from ..state import State
from ..environment import Environment
from ..mission import Mission, MissionOutcome
from ..action import Action, Parameter
from ..valueRange import DiscreteValueRange


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
    def domain(self) -> List[Tuple[int, str, List[Parameter]]]:
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
        domain = []
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


    def generate_mission(self, environment: Environment, initial_state: State, rng) -> Mission:
        """
        Return a mission in this domain.
        """
        actions = []
        for _, schema, params in self.domain:
            actions.append(Action(schema, {p.name: p.generate(rng) for p in params}))
        return Mission(environment, initial_state, actions)


class RootCauseFinder(object):
    """
    RootCauseFinder is used to find minimum requirements that
    results in mission failure the same way that initial failing
    missions do. 
    """
    def __init__(self, system: System, initial_state: State, environment: Environment, initial_failing_missions: List[Mission], random_seed=100):
        assert(len(initial_failing_missions) > 0)

        self.__system = system
        self.__initial_state = initial_state
        self.__environment = environment
        self.__rng = random.Random(random_seed)
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
        the initial state used for running all missions.
        """
        return self.__initial_state


    @property
    def environment(self):
        """
        the environment used for running all missions.
        """
        return self.__environment


    @property
    def initial_failing_missions(self):
        """
        the failing missions provided by the user.
        """
        return self.__initial_failing_missions


    @property
    def rng(self):
        return self.__rng


    def find_root_cause(self, time_limit=None) -> MissionDomain:
        """
        The main function that finds the root cause.
        """
        raise NotImplementedError

