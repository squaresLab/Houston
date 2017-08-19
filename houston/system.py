# TODO: rename `OutcomeBranch` to `Branch`
import copy
import json
import state
import mission
import timeit
import signal
import math

from util import TimeoutError


class System(object):
    """
    Description of System.
    """


    def __init__(self, identifier, variables, schemas):
        """
        Constructs a new System.

        :param  identifier: a unique string identifier (i.e., a name) for this\
                            system
        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
        assert (isinstance(identifier, str) and not None)
        assert (isinstance(variables, dict) and not None)
        self.__identifier = identifier
        self.__variables = variables
        self.__schemas = schemas


    def installed(self):
        """
        Returns true if this system is installed on this machine.
        """
        raise NotImplementedError


    def getIdentifier(self):
        """
        Returns the unique identifier (i.e., the name) for this system.
        """
        return self.__identifier

   
    def getBranches(self):
        """
        Returns a list of the branches for this system.
        """
        return [b for s in s.__schemas for b in s.getBranches()]


    def getBranch(self, iden):
        """
        Returns an outcome branch for this sytem provided its identifier.
        """
        assert (isinstance(iden, BranchID) and iden is not None)
        schema = self.__schemas[iden.getActionName()]
        return schema.getBranch(iden)


    def setUp(self, mission):
        """
        Responsible for appropriately configuring and launching the system,
        for a given mission.
        """
        raise NotImplementedError


    def tearDown(self, mission):
        """
        Responsible for safely closing the system, following the execution of
        a given mission.
        """
        raise NotImplementedError


    def execute(self, msn):
        """
        Executes a given mission.

        :param  msn:    the mission that should be executed.

        :return A summary of the outcome of the mission, in the form of a
                MissionOutcome
        """
        assert (self.installed())
        timeBeforeSetup = timeit.default_timer()
        self.setUp(msn)
        totalSetupTime = timeit.default_timer() - timeBeforeSetup

        env = msn.getEnvironment()
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.getActions():
                schema = self.__schemas[action.getSchemaName()]

                # compute expected state
                initialState = self.getState()

                # resolve the branch and compute the expected outcome
                branch = schema.resolveBranch(action, initialState, env)
                expected = branch.computeExpectedState(action, initialState, env)

                # enforce a timeout
                timeout = schema.computeTimeout(action, initialState, env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                timeBefore = timeit.default_timer()

                try:
                    schema.dispatch(action, initialState, env)
                except TimeoutError:
                    pass
                finally:
                    signal.alarm(0) # does this reset the alarm?

                timeAfter = timeit.default_timer()
                timeElapsed = timeAfter - timeBefore

                print('Doing: {}'.format(action.getSchemaName()))

                # compare the observed and expected states
                observed = self.getState()
                passed = expected.isExpected(self.__variables, observed)
                outcome = mission.ActionOutcome(action, passed, initialState, observed, timeElapsed, branch.getID())
                outcomes.append(outcome)

                if not passed:
                    totalTime = timeit.default_timer() - timeBeforeSetup
                    return mission.MissionOutcome(False, outcomes, totalSetupTime, \
                                                                        totalTime)
            totalTime = timeit.default_timer() - timeBeforeSetup
            return mission.MissionOutcome(True, outcomes, totalSetupTime, totalTime)

        finally:
            self.tearDown(msn)


    def getState(self):
        """
        Returns a description of the current state of the system.

        TODO: ensure that the system is actually running!
        """
        assert (self.installed())
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return state.State(vals)


    def getActionSchemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)


class OutcomeBranch(object):
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

        assert (isinstance(schema, ActionSchema) and schema is not None)
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
        return BranchID(self.__schema, self.__name)


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


    def isApplicable(self, action, initialState, env):
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


    def computeTimeout(self, action, state, environment):
        """
        Computes the timeout for the current branch.
        """
        raise NotImplementedError


    def computeExpectedState(self, action, initialState, env):
        """
        Produces an estimate of the system state following the execution of
        this branch within a given context.

        :param  action:         a description of the action being performed
        :param  initialState:   the state of the system immediately prior to \
                                the execution of this action
        :param  env:            the environment in which the action is being \
                                performed

        :returns    An ExpectedState object, describing the state that the \
                    system is expected to be in immediately after the \
                    execution of this branch
        """
        assert (isinstance(action, mission.Action) and action is not None)
        assert (isinstance(initialState, state.State) and state is not None)
        assert (isinstance(env, state.Environment) and env is not None)


        # store the expected state values in a dictionary, indexed by the name
        # of the associated state variable
        values = {}
        for (varName, initialValue) in initialState.getValues().items():
            if varName in self.__effects:
                expected = self.__effects[varName].computeExpectedValue(action, initialState, env)
                values[varName] = expected
            else:
                values[varName] = state.ExpectedStateValue(initialValue)

        return state.ExpectedState(values)


class IdleBranch(OutcomeBranch):
    def __init__(self):
        super(IdleBranch, self).__init__([])

    def computeTimeout(self, action, state, environment):
        return 1.0

    def isApplicable(self, action, state, environment):
        return True


class ActionSchema(object):
    """
    Action schemas are responsible for describing the kinds of actions that
    can be performed within a given system. Action schemas describe actions
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """

    def __init__(self, name, parameters, branches):
        """
        Constructs an ActionSchema object.

        :param  name            name of the action schema
        :param  parameters      a list of the parameters for this action schema
        :param  branches        a list of the possible outcomes for actions \
                                belonging to this schema. If none of the \

        """
        assert (isinstance(name, str) and not name is None)
        assert (len(name) > 0)
        assert (isinstance(parameters, list) and not parameters is None)
        assert (all(isinstance(p, Parameter) for p in parameters))
        assert (isinstance(branches, list) and not branches is None)
        assert (all(isinstance(b, OutcomeBranch) for b in branches))
        assert (len(branches) > 0)

        # unique branch names
        assert (len(set(b.getName() for b in branches)) == len(branches))

        self.__name = name
        self.__parameters =  parameters
        self.__branches = branches


    def getName(self):
        """
        Returns the name of this schema.
        """
        return self.__name


    def getBranches(self):
        """
        Returns a list of the branches for this action schema.
        """
        return self.__branches[:]

    
    def getBranch(self, iden):
        """
        Returns a branch belonging to this action schema using its identifier.
        """
        assert (isinstance(iden, BranchID) and iden is not None)
        assert (iden.getActionName() == self.__name)
        return self.__branches[iden.getBranchName()]


    def dispatch(self, action, state, environment):
        """
        Responsible for invoking an action belonging to this schema.

        :param  action  an Action belonging to this schema
        """
        raise UnimplementedError


    def computeTimeout(self, action, state, environment):
        """
        Responsible for calculating the maximum time that this action shoud take.

        :param  action          the action that is going to be performed.
        :param  state           the state in which the system is currently on.
        :param  environment     the system environment

        :returns maximum time in seconds (as a float)
        """
        branch = self.resolveBranch(action, state, environment)
        return branch.computeTimeout(action, state, environment)


    def getParameters(self):
        """
        Returns the parameters being hold for the current action schema. This is
        used to generate actions
        """
        return copy.deepcopy(self.__parameters)


    def resolveBranch(self, action, initialState, environment):
        """
        Returns the branch that is appropiate for the current action, state, and
        environment based on the current action schema.
        """
        branch = None
        for b in self.__branches:
            if b.isApplicable(action, initialState, environment):
                return b
        raise Exception


    def generate(self):
        """
        Generates an action belonging to this schema at random.
        """
        values = {p.getName(): p.generate() for p in self.__parameters}
        return mission.Action(self.__name, values)


class ActionGenerator(object):

    def __init__(self, schemaName, parameters = []):
        """
        Constructs a new action generator.

        :param  schemaName: the name of the schema for which this generator \
                    produces actions.
        :params parameters: a list of the parameters to this generator.
        """
        assert (isinstance(schemaName, str) and schemaName is not None)
        assert (isinstance(parameters, list) and parameters is not None)

        self.__schemaName = schemaName
        self.__parameters = parameters


    def constructWithState(self, currentState, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError


    def constructWithoutState(self, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError


    def getSchemaName(self):
        """
        Returns the name of the schema to which actions generated by this
        generator belong.
        """
        return self.__schemaName


    def generateActionWithState(self, currentState, env):
        values = {p.getName(): p.generate() for p in self.__parameters}
        values = self.constructWithState(currentState, env, values)
        return mission.Action(self.__schemaName, values)


    def generateActionWithoutState(self, env):
        values = {p.getName(): p.generate() for p in self.__parameters}
        values = self.constructWithoutState(env, values)
        return mission.Action(self.__schemaName, values)


class BranchID(object):
    @staticmethod
    def fromJSON(jsn):
        # TODO: fix earlier string assertions!
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
        elif isinstance(b, OutcomeBranch):
            return BranchPath(self.__identifiers + [b.getID()])
        else:
            raise Exception('BranchPath::extended expected a BranchID or OutcomeBranch object')


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
