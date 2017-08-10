import thread
import time
import copy
import json
import state
import mission

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

    def systemAlive(self):
        """
        Returns true if system is running.
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
        self.setUp(msn)

        env = msn.getEnvironment()
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.getActions():
                schema = self.__schemas[action.getSchemaName()]

                initialState = self.getState()
                expected = schema.computeExpectedState(action, initialState, env)

                # dispatch (blocks until action completion)
                actionTimeout = schema.computeTimeout(action, initialState, environment)
                schema.dispatch(action)
                print('Doing: {}'.format(action.getSchemaName()))

                # compare the observed and expected states
                observed = self.getState()
                passed = expected.isExpected(observed)
                outcome = mission.ActionOutcome(action, passed, initialState, observed)
                outcomes.append(outcome)

                if not passed:
                    return mission.MissionOutcome(False, outcomes)

            return mission.MissionOutcome(True, outcomes)

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
    def __init__(self, guard, effects = []):
        assert (callable(guard))
        assert (isinstance(effects, list) and not effects is None)
        assert (all(isinstance(e, state.Estimator) for e in effects))

        self.__guard = guard
        self.__effect = effects


    def isGuardSatisfied(self, action, initialState, env):
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
        return self.__guard(action, initialState, env)


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
        values = {}

        for (varName, initialValue) in initialState.getValues():
            if varName in self.__effects:
                expected = effects[varName].computeExpectedValue(action, initialState, env)
                values[varName] = expected
            else:
                values[varName] = ExpectedStateValue(initialValue)

        return state.ExpectedState(values)


class OutcomeElseBranch(OutcomeBranch):
    def __init__(self, effects = []):
        super(OutcomeElseBranch, self).__init__(lambda a, s, e: True, effects)


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


    def dispatch(self, action):
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
        raise UnimplementedError


    def getParameters(self):
        """
        Returns the parameters being hold for the current action schema. This is
        used to generate actions
        """
        return copy.deepcopy(self.__parameters)


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
        # figure out which branch the action is expected to take.
        branch = None
        for b in self.__branches:
            if b.isApplicable(action, initialState, environment):
                branch = b
                break

        # if no branch is applicable, the system state is assumed to remain
        # unchanged following the execution of the action
        if branch is None:
            return state.ExpectedState.identical(initialState) # TODO implement

        return branch.computeExpectedState(action, initialState, environment)
