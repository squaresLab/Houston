from typing import List, Iterator, Union

import random

from .util import printflush
from .state import State, Environment
from .specification import Specification


class BranchID(object):
    @staticmethod
    def from_string(s: str) -> 'BranchID':
        action_name, _, branch_name = s.partition(':')
        return BranchID(action_name, branch_name)

    def __init__(self,
                 action_name: str,
                 branch_name: str):
        assert action_name is not ''
        assert branch_name is not ''

        self.__action_name = str(action_name)
        self.__branch_name = str(branch_name)

    def equals(self, other: 'BranchID') -> bool:
        return self.__eq__(other)

    def __eq__(self, other: 'BranchID') -> bool:
        return self.__action_name == other.schema_name and \
               self.__branch_name == other.branch_name

    @property
    def schema_name(self) -> str:
        """
        The name of the schema to which this branch identifier belongs.
        """
        return self.__action_name

    @property
    def branch_name(self) -> str:
        """
        The (unqualified) name of the branch to which this identifier belongs.
        """
        return self.__branch_name

    def __str__(self) -> str:
        return "{}:{}".format(self.__action_name, self.__branch_name)

    def __repr__(self):
        r = "BranchID(\"{}\", \"{}\")"
        r = r.format(self.schema_name, self.branch_name)
        return r


class Branch(object):
    """
    Describes a possible behaviour of an action via a specification over the
    state of the system before and after executing the action.
    """
    def __init__(self,
                 name: str,
                 schema: 'ActionSchema',
                 specification: Specification
                 ) -> None:
        """
        Constructs a new outcome branch.

        Parameters:
            name: the name of the branch.
            schema: the action schema to which this outcome branch belongs.
        """
        from houston.action import ActionSchema  # FIXME
        assert name is not ""
        self.__name = name
        self.__schema = schema
        self.__specification = specification

    @property
    def schema(self) -> 'ActionSchema':
        return self.__schema

    @property
    def name(self) -> str:
        return self.__name

    @property
    def specification(self) -> Specification:
        return self.__specification

    @property
    def id(self) -> BranchID:
        return BranchID(self.__schema.name, self.__name)

    def generate(self, system, initial_state, env, rng) -> 'Action':
        """
        Generates an action that would cause the system to take this branch.

        :param  initialState:   the state of the system immediately before \
                                executing the generated action.
        :param  env:            the environment in which the mission will be \
                                conducted.
        :param  rng:            the random number generator
        """
        raise NotImplementedError

    def is_satisfiable(self,
                       system: 'System',
                       initial_state: State,
                       environment: Environment
                       ) -> bool:
        """
        Determines whether there exists a set of parameter values that would
        satisify this precondition given a fixed initial state and
        environment.
        """
        return self.specification.precondition.is_satisfiable(system, initial_state, env)

    def precondition(self,
                     system: 'System',
                     action: 'Action',
                     state: State,
                     environment: Environment) -> bool:
        """
        Determines whether the guard for this outcome branch is satisfied by
        the parameters for the action, the state of the system immediately
        prior to the execution of the action, and the state of the environment.

        :param  action:         a description of the action that is about to \
                                be performed
        :param  initialState:   the state of the system immediately prior to \
                                the execution of the action
        :param  env:            the environment in which the action is being \
                                performed

        :returns    True if the guard is satisfied by the given context, \
                    otherwise False.
        """
        return self.specification.precondition.is_satisfied(system, action.values, state, None, environment)

    def postcondition(self,
                      system: 'System',
                      action: 'Action',
                      state_before: State,
                      state_after: State,
                      environment: Environment) -> bool:
        return self.specification.postcondition.is_satisfied(system, action.values,
                state_before, state_after, environment)

    def timeout(self,
                system: 'System',
                act: 'Action',
                state: State,
                environment: Environment
                ) -> float:
        """
        Computes the maximum length of time that is required to execute a
        given action (that will traverse this branch) in a particular state
        and environment.

        Returns:
            maximum length of time given in seconds.
        """
        return self.specification.timeout()


class IdleBranch(Branch):
    
    def __init__(self, schema: 'ActionSchema',
                parameters: List['Parameters']=None,
                idle_time: float=5.0) -> None:
        assert isinstance(idle_time, float)
        assert idle_time > 0
        self.__idle_time = idle_time
        specification = Specification(parameters,
                """
                (true)
                """,
                """
                (and (= _latitude __latitude)
                    (= _longitude __longitude)
                    (= _altitude __altitude)
                    (= _armed __armed)
                    (= _armable __armable)
                    (= _mode __mode))
                """,
                None)
        super(IdleBranch, self).__init__("idle", schema, specification)

    def timeout(self, system, action, state, environment):
        return self.__idle_time + 2.0

    def precondition(self,
                     system: 'System',
                     action: 'Action',
                     state: State,
                     environment: Environment
                     ) -> bool:
        return True

    def postcondition(self,
                      system: 'System',
                      action: 'Action',
                      state_before: State,
                      state_after: State,
                      environment: Environment
                      ) -> bool:
        time_passed = state_after.time_offset - state_before.time_offset
        reached_idle_time = time_passed > self.__idle_time
        remained_same = self.are_states_equal(system,
                                              state_before,
                                              state_after)
        return reached_idle_time and remained_same

    def is_satisfiable(self, system, state, environment):
        return True

    def generate(self,
                 system: 'System',
                 state: State,
                 environment: Environment,
                 rng: random.Random
                 ) -> 'Action':
        return self.schema.generate(rng)

    def are_states_equal(self,
                         system: 'System',
                         state_before: State,
                         state_after: State
                         ) -> bool:
        for v in system.variables.keys():
            if not system.variable(v).eq(state_before[v], state_after[v]):
                return False
        return True


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
    #@property
    def branches(self, system: 'System') -> List[Branch]:
        """
        Returns an ordered list of the branches along this path.
        """
        return [system.branch(i) for i in self.__identifiers]

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
