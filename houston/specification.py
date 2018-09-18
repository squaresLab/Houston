__all__ = ['Specification', 'Idle']

from typing import List, Iterator, Union
import random

import attr

from .state import State
from .environment import Environment
from .configuration import Configuration


@attr.s
class Specification(object):
    name = attr.ib(type=str)

    """
    Describes a possible behaviour of an action via a specification over the
    state of the system before and after executing the action.
    """
    def generate(self,
                 state: State,
                 env: Environment,
                 config: Configuration,
                 rng: random.Random
                 ) -> 'Action':
        """
        Generates an action that would cause the system to take this branch.
        """
        raise NotImplementedError

    def is_satisfiable(self,
                       state: State,
                       environment: Environment,
                       configuration: Configuration
                       ) -> bool:
        """
        Determines whether there exists a set of parameter values that would
        satisify this precondition given a fixed initial state and
        environment.
        """
        raise NotImplementedError

    def precondition(self,
                     action: 'Action',
                     state: State,
                     environment: Environment,
                     configuration: Configuration
                     ) -> bool:
        raise NotImplementedError

    def postcondition(self,
                      action: 'Action',
                      state_before: State,
                      state_after: State,
                      environment: Environment,
                      configuration: Configuration
                      ) -> bool:
        raise NotImplementedError

    def timeout(self,
                action: 'Action',
                state: State,
                environment: Environment,
                configuration: Configuration
                ) -> float:
        """
        Computes the maximum length of time that is required to execute a
        given action (that will traverse this branch) in a particular state
        and environment.

        Returns:
            maximum length of time given in seconds.
        """
        raise NotImplementedError


class Idle(Specification):
    def __init__(self, idle_time: float = 5.0) -> None:
        assert idle_time > 0
        self.__idle_time = idle_time
        super().__init__("idle")

    def timeout(self, system, action, state, environment):
        return self.__idle_time + 2.0

    def precondition(self,
                     action: 'Action',
                     state: State,
                     environment: Environment,
                     configuration: Configuration
                     ) -> bool:
        return True

    def postcondition(self,
                      action: 'Action',
                      state_before: State,
                      state_after: State,
                      environment: Environment,
                      configuration: Configuration
                      ) -> bool:
        time_passed = state_after.time_offset - state_before.time_offset
        reached_idle_time = time_passed > self.__idle_time
        remained_same = state_before.equiv(state_after)
        return reached_idle_time and remained_same

    def is_satisfiable(self, system, state, environment):
        return True

    def generate(self,
                 state: State,
                 environment: Environment,
                 configuration: Configuration,
                 rng: random.Random
                 ) -> 'Action':
        return self.schema.generate(rng)
