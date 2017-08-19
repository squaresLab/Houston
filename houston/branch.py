import state
import action
import mission # TODO: CIRCULAR


class Branch(object):
    def __init__(self, name, schema, estimators):
        """
        Constructs a new outcome branch.

        :param  name:           the name of this branch.
        :param  schema:         the action schema to which this outcome \
                                branch belongs, given as an ActionSchema \
                                instance.
        :param  estimators:     a list of state estimators for this branch.
        """
        assert (isinstance(estimators, list) and estimators is not None)
        assert (all(isinstance(e, state.Estimator) for e in estimators))

        self.__effects = {e.getVariableName(): e for e in estimators}
        assert (isinstance(self.__effects, dict) and self.__effects is not None)

        assert (isinstance(name, str))
        assert (name is not None)
        assert (name is not "")
        self.__name = name

        assert (isinstance(schema, action.ActionSchema) and schema is not None)
        self.__schema = schema


    def getSchema(self):
        """
        Returns the action schema to which this outcome branch belongs.
        """
        return self.__schema


    def getSchemaName(self):
        """
        Returns the name of the schema to which this outcome branch belongs.
        """
        return self.getSchema().getName()


    def getName(self):
        """
        Returns the name of this branch.
        """
        return self.__name


    def getID(self):
        """
        Returns the identifier for this branch.
        """
        return BranchID(self.getSchemaName(), self.__name)


    def generate(self, initialState, env):
        """
        Generates an action that would cause the system to take this branch.

        :param  initialState:   the state of the system immediately before \
                                executing the generated action.
        :param  env:            the environment in which the mission will be \
                                conducted.
        """
        raise NotImplementedError


    def isSatisfiable(self, initialState, env):
        """
        Determines whether there exists a set of parameter values that would
        satisify this precondition given a fixed initial state and
        environment.
        """
        raise NotImplementedError


    def isApplicable(self, act, initialState, env):
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
        raise NotImplementedError


    def computeTimeout(self, act, state, environment):
        """
        Computes the timeout for the current branch.
        """
        raise NotImplementedError


    def computeExpectedState(self, act, initialState, env):
        """
        Produces an estimate of the system state following the execution of
        this branch within a given context.

        :param  act:            a description of the action being performed
        :param  initialState:   the state of the system immediately prior to \
                                the execution of this action
        :param  env:            the environment in which the action is being \
                                performed

        :returns    An ExpectedState object, describing the state that the \
                    system is expected to be in immediately after the \
                    execution of this branch
        """
        assert (isinstance(act, action.Action) and act is not None)
        assert (isinstance(initialState, state.State) and state is not None)
        assert (isinstance(env, state.Environment) and env is not None)


        # store the expected state values in a dictionary, indexed by the name
        # of the associated state variable
        values = {}
        for (varName, initialValue) in initialState.getValues().items():
            if varName in self.__effects:
                expected = self.__effects[varName].computeExpectedValue(act, initialState, env)
                values[varName] = expected
            else:
                values[varName] = state.ExpectedStateValue(initialValue)

        return state.ExpectedState(values)


class IdleBranch(Branch):
    def __init__(self, schema):
        super(IdleBranch, self).__init__("idle", schema, [])


    def computeTimeout(self, act, state, environment):
        return 1.0


    def isApplicable(self, act, state, environment):
        return True


    def isSatisfiable(self, state, environment):
        return True


    def generate(self, state, environment):
        return self.getSchema.generate()


class BranchID(object):
    @staticmethod
    def fromJSON(jsn):
        assert (isinstance(jsn, str) or isinstance(jsn, unicode))
        assert (jsn is not None)
        assert (jsn != '')

        (actionName, _, branchName) = jsn.partition(':')

        return BranchID(actionName, branchName)

    
    def __init__(self, actionName, branchName):
        assert (isinstance(actionName, str) or isinstance(actionName, unicode))
        assert (actionName is not None)
        assert (actionName is not '')
        # TODO: rules
        assert (isinstance(branchName, str) or isinstance(branchName, unicode))
        assert (branchName is not None)
        assert (branchName is not '')
        # TODO: rules

        self.__actionName = actionName
        self.__branchName = branchName


    def __eq__(self, other):
        return  self.__actionName == other.getActionName() and \
                self.__branchName == other.getBranchName()

    
    def getActionName(self):
        return self.__actionName


    def getBranchName(self):
        return self.__branchName


    def __str__(self):
        return "{}:{}".format(self.__actionName, self.__branchName)


    def __repr__(self):
        return str(self)
 

class BranchPath(object):
    def __init__(self, identifiers):
        assert (isinstance(identifiers, list) and identifiers is not None)
        assert (all(isinstance(i, BranchID) for i in identifiers))
        self.__identifiers = identifiers


    def length(self):
        """
        Returns the length of this path (measured by its number of branches).
        """
        return len(self.__identifiers)


    def getIdentifiers(self):
        """
        Returns an ordered list of identifiers for the branches along this path.
        """
        return copy.copy(self.__identifiers)


    def getBranches(self, systm):
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
            return BranchPath(self.__identifiers + [b.getID()])
        else:
            raise Exception('BranchPath::extended expected a BranchID or Branch object')


    def startswith(self, prefix):
        """
        Determines whether this path is prefixed by a given path. Returns True
        if this path is prefixed by the given path, otherwise False.
        """
        assert (isinstance(prefix, BranchPath) and prefix is not None)

        if prefix.length() > self.length():
            return False

        prefix = prefix.getIdentifiers()
        for i in range(len(prefix)):
            if prefix[i] != self.__identifiers[i]:
                return False

        return True


    def __eq__(self, other):
        assert (isinstance(other, BranchPath) and not BranchPath is None)
        if self.size() != other.size():
            return False
        for (x, y) in zip(self.__identifiers, other.getIdentifiers()):
            if x != y:
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
