__all__ = ['BranchID', 'Branch', 'IdleBranch', 'BranchPath']

from typing import List, Iterator, Union
import random

import attr

from .state import State
from .environment import Environment
from .configuration import Configuration


@attr.s(frozen=True)
class BranchID(object):
    name_action = attr.ib(type=str)
    name_branch = attr.ib(type=str)

    @staticmethod
    def from_string(s: str) -> 'BranchID':
        action_name, _, branch_name = s.partition(':')
        return BranchID(action_name, branch_name)

    def __str__(self) -> str:
        return "{}:{}".format(self.name_action, self.name_branch)


class Branch(object):
    """
    Describes a possible behaviour of an action via a specification over the
    state of the system before and after executing the action.
    """
    def __init__(self,
                 name_schema: str,
                 name_branch: str,
                 ) -> None:
        """
        Constructs a new outcome branch.

        Parameters:
            name_schema: the name of the schema to which the branch belongs.
            name_branch: the name of the branch.
        """
        assert name_schema is not ""
        assert name_branch is not ""
        self.__name_schema = name_schema
        self.__name_branch = name_branch

    @property
    def name(self) -> str:
        return "{}:{}".format(self.__name_schema, self.__name_branch)

    @property
    def id(self) -> BranchID:
        return BranchID(self.__name_schema, self.__name_branch)

    def generate(self,
                 state: State,
                 env: Environment,
                 config: Configuration,
                 rng: random.Random) -> 'Action':
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


class IdleBranch(Branch):
    def __init__(self,
                 name_schema: str,
                 idle_time: float = 5.0
                 ) -> None:
        assert idle_time > 0
        self.__idle_time = idle_time
        super().__init__(name_schema, "idle")

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


class BranchPath(object):
    """
    Describes a sequence of branches that were taken during the execution of
    a mission.
    """
    def __init__(self,
                 identifiers: List[BranchID]
                 ) -> None:
        self.__identifiers = identifiers

    @property
    def length(self) -> int:
        """
        Returns the length of this path (measured by its number of branches).
        """
        return len(self.__identifiers)

    def __iter__(self) -> Iterator[BranchID]:
        yield from self.__identifiers

    # FIXME deprecate!
    @property
    def identifiers(self):
        """
        An ordered list of identifiers for the branches along this path.
        """
        return self.__identifiers[:]

    # FIXME this is nasty
    @property
    def branches(self, system: 'System') -> List[Branch]:
        """
        Returns an ordered list of the branches along this path.
        """
        return [system.getBranch(i) for i in self.__identifiers]

    # FIXME avoid Union
    def extended(self, b: Union[BranchID, Branch]) -> 'BranchPath':
        """
        Returns a variant of this branch path with an additional branch
        appended to its end.
        """
        if isinstance(b, BranchID):
            return BranchPath(self.__identifiers + [b])
        elif isinstance(b, Branch):
            return BranchPath(self.__identifiers + [b.id])
        else:
            raise Exception('Expected a BranchID or Branch object')

    def startswith(self, prefix: 'BranchPath') -> bool:
        """
        Determines whether this path is prefixed by a given path. Returns True
        if this path is prefixed by the given path, otherwise False.
        """
        if prefix.length > self.length:
            return False

        prefix = prefix.identifiers
        for i in range(len(prefix)):
            if prefix[i] != self.__identifiers[i]:
                return False

        return True

    def __hash__(self) -> int:
        return hash(tuple(str(i) for i in self.__identifiers))

    def __eq__(self, other: 'BranchPath') -> bool:
        if self.length != other.length:
            return False
        for (x, y) in zip(self.__identifiers, other.identifiers):
            if not x.equals(y):
                return False
        return True

    def __str__(self) -> str:
        s = ', '.join([str(i) for i in self.__identifiers])
        s = '<{}>'.format(s)
        return s

    def __repr__(self) -> str:
        return 'BranchPath({})'.format(str(self))
