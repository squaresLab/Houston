import houston.state
import houston.mission
import random

from houston.util import printflush
from houston.specification import Specification


class Branch(object):
    def __init__(self, name, schema, specification: Specification):
        """
        Constructs a new outcome branch.

        :param  name:           the name of this branch.
        :param  schema:         the action schema to which this outcome \
                                branch belongs, given as an ActionSchema \
                                instance.
        """
        from houston.action import ActionSchema
        assert isinstance(name, str)
        assert (name is not "")
        self.__name = name

        assert isinstance(schema, ActionSchema)
        self.__schema = schema

        self.__specification = specification


    @property
    def schema(self):
        """
        The action schema to which this outcome branch belongs.
        """
        return self.__schema


    @property
    def name(self):
        """
        The name of this branch.
        """
        return self.__name

    
    @property
    def specification(self):
        """
        Specifications of this branch
        """
        return self.__specification


    @property
    def id(self):
        """
        The identifier for this branch.
        """
        return BranchID(self.__schema.name, self.__name)


    def generate(self, system, initial_state, env, rng):
        """
        Generates an action that would cause the system to take this branch.

        :param  initialState:   the state of the system immediately before \
                                executing the generated action.
        :param  env:            the environment in which the mission will be \
                                conducted.
        :param  rng:            the random number generator
        """
        raise NotImplementedError


    def is_satisfiable(self, system, initial_state, env):
        """
        Determines whether there exists a set of parameter values that would
        satisify this precondition given a fixed initial state and
        environment.
        """
        return self.specification.precondition.is_satisfiable(system, initial_state, env)


    def precondition(self, system, action, state, env):
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
        return self.specification.precondition.is_satisfied(system, action.values, state, None, env)


    def postcondition(self, system, action, state_before, state_after, environment):
        return self.specification.postcondition.is_satisfied(system, action.values,
                state_before, state_after, environment)


    def timeout(self, system, act, state, environment):
        """
        Computes the timeout for the current branch.
        """
        return self.specification.timeout()


class IdleBranch(Branch):
    def __init__(self, schema, parameters=None, idle_time=5.0):
        assert isinstance(idle_time, float)
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


    def precondition(self, system, action, state, environment):
        return True


    def postcondition(self, system, action, state_before, state_after, environment):
        return (state_after.time_offset - state_before.time_offset) > self.__idle_time \
               and self.are_states_equal(system, state_before, state_after)


    def is_satisfiable(self, system, state, environment):
        return True


    def generate(self, system, state, environment, rng):
        assert isinstance(rng, random.Random)
        return self.schema.generate(rng)


    def are_states_equal(self, system, state_before, state_after):
        from houston.state import State
        assert isinstance(state_before, State)
        assert isinstance(state_after, State)

        for v in system.variables.keys():
            if not system.variable(v).eq(state_before[v], state_after[v]):
                return False
        return True


class BranchID(object):
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, str) or isinstance(jsn, unicode)
        assert (jsn != '')

        (action_name, _, branch_name) = jsn.partition(':')

        return BranchID(action_name, branch_name)

    
    def __init__(self, action_name, branch_name):
        assert (isinstance(action_name, str) or isinstance(action_name, unicode))
        assert (action_name is not '')
        # TODO: rules
        assert (isinstance(branch_name, str) or isinstance(branch_name, unicode))
        assert (branch_name is not '')
        # TODO: rules

        self.__action_name = str(action_name)
        self.__branch_name = str(branch_name)


    def equals(self, other):
        return self.__eq__(other)


    def __eq__(self, other):
        return  self.__actionName == other.schema_name and \
                self.__branchName == other.branch_name

    
    @property
    def schema_name(self):
        """
        The name of the schema to which this branch identifier belongs.
        """
        return self.__action_name


    @property
    def branch_name(self):
        """
        The (unqualified) name of the branch to which this identifier belongs.
        """
        return self.__branch_name


    def __str__(self):
        return "{}:{}".format(self.__action_name, self.__branch_name)


    def __repr__(self):
        return str(self)


    def to_json(self):
        return str(self)


class BranchPath(object):
    def __init__(self, identifiers):
        assert (isinstance(identifiers, list) and identifiers is not None)
        assert (all(isinstance(i, BranchID) for i in identifiers))
        self.__identifiers = identifiers


    @property
    def length(self):
        """
        Returns the length of this path (measured by its number of branches).
        """
        return len(self.__identifiers)


    @property
    def identifiers(self):
        """
        An ordered list of identifiers for the branches along this path.
        """
        return self.__identifiers[:]


    @property
    def branches(self, systm):
        """
        Returns an ordered list of the branches along this path.
        """
        return [systm.getBranch(i) for i in self.__identifiers]


    def extended(self, b):
        """
        Returns a copy of this path with an additional branch attached to the
        end.

        :param  branchID:   the branch that should be added to this path, \
                            given as an identifier or a branch object 
        """
        assert (b is not None)
        if isinstance(b, BranchID):
            return BranchPath(self.__identifiers + [b])
        elif isinstance(b, Branch):
            return BranchPath(self.__identifiers + [b.id])
        else:
            raise Exception('BranchPath::extended expected a BranchID or Branch object')


    def startswith(self, prefix):
        """
        Determines whether this path is prefixed by a given path. Returns True
        if this path is prefixed by the given path, otherwise False.
        """
        assert isinstance(prefix, BranchPath)

        if prefix.length > self.length:
            return False

        prefix = prefix.identifiers
        for i in range(len(prefix)):
            if prefix[i] != self.__identifiers[i]:
                return False

        return True


    def __hash__(self):
        return hash(tuple(str(i) for i in self.__identifiers))


    def __eq__(self, other):
        assert isinstance(other, BranchPath)
        if self.length != other.length:
            return False
        for (x, y) in zip(self.__identifiers, other.identifiers):
            if not x.equals(y):
                return False
        return True


    def __str__(self):
        """
        Returns a string-based description of this path.
        """
        s = ', '.join([str(i) for i in self.__identifiers])
        s = '<{}>'.format(s)
        return s

    
    def __repr__(self):
        return str(self)
