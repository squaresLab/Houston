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
                expected = schema.computeExpectedState(action, initialState, env)

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
                outcome = mission.ActionOutcome(action, passed, initialState,
                                                observed, timeElapsed)
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
    def __init__(self, label, estimators):
        assert (isinstance(estimators, list) and estimators is not None)
        assert (all(isinstance(e, state.Estimator) for e in estimators))

        self.__effects = {e.getVariableName(): e for e in estimators}
        assert (isinstance(self.__effects, dict) and self.__effects is not None)

        assert (isinstance(name, str) or isinstance(name, unicode))
        assert (name is not None)
        assert (name is not "")
        self.__name = name


    def getName(self):
        """
        Returns the name of this branch.
        """
        return self.__label


    def generate(self, initialState, env):
        pass


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
        assert (isinstance(branches, list) and not branches is None)
        assert (len(branches) > 0)

        self.__name = name
        self.__parameters =  parameters
        self.__branches = branches


    def getName(self):
        """
        Returns the name of this schema.
        """
        return self.__name


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


    def computeExpectedState(self, action, initialState, environment):
        """
        Estimates the resulting system state after executing an action
        belonging to this schema in a given initial state.

        :param  action:         the action for which an outcome should be \
                                estimated.
        :param  initialState:   the initial state of the system, immediately \
                                prior to executing the action.
        :param  environment:    a description of the environment in which the \
                                action should take place.

        :return An estimate of the resulting system state, in the form of an \
                ExpectedState object
        """
        assert (isinstance(action, mission.Action) and action is not None)
        assert (isinstance(initialState, state.State) and state is not None)
        assert (isinstance(environment, state.Environment) and environment is not None)

        branch = self.resolveBranch(action, initialState, environment)
        # if no branch is applicable, the system state is assumed to remain
        # unchanged following the execution of the action
        if branch is None:
            return state.ExpectedState.identical(initialState)

        return branch.computeExpectedState(action, initialState, environment)


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


class BranchPath(object):

    def __init__(self, branches):
        assert (isinstance(branches, list) and branches is not None)
        assert (branches is not [])
        # TODO: assert type of elements in `branches`
        assert (all(isinstance(b, OutcomeBranch) for b in branches))
        self.__branches = branches


    def length(self):
        """
        Returns the length of this path (measured by its number of branches).
        """
        return len(self.__branches)


    def getBranches(self):
        """
        Returns an ordered list of the branches along this path.
        """
        return copy.copy(self.__branches)


    def extended(self, branch):
        """
        Returns a copy of this path with an additional branch attached to the end.
        """
        return BranchPath(self.__branches + [branch])


    def startswith(self, prefix):
        """
        Determines whether this path is prefixed by a given path. Returns True
        if this path is prefixed by the given path, otherwise False.
        """
        if prefix.length() > self.length():
            return False

        prefix = prefix.getBranches()
        for i in range(len(prefix)):
            if prefix[i] != self.__branches[i]:
                return False

        return True


    def __str__(self):
        """
        Returns a string-based description of this path.
        """
        s = ', '.join([str(b) for b in self.__branches])
        s = '<{}>'.format(s)
        return s

    
    def __repr__(self):
        return str(self)
