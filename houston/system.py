import thread
import time
import copy
import json
import state

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


    def identifier(self):
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


    def execute(self, mission):
        """
        Executes a given mission.

        :param  mission:    the mission that should be executed.

        :return A summary of the outcome of the mission, in the form of a
                MissionOutcome
        """
        assert (self.installed())
        self.setUp(mission)
        try:

            outcomes = []
            for action in mission.getActions():
                schema = self.__schemas[action.getSchemaName()]
                stateBefore = self.getInternalState()

                # check for precondition violations
                (satisfied, violations) = \
                    schema.satisfiedPreconditions(self.__variables, action)
                if not satisfied:
                    stateAfter = self.getInternalState()
                    outcome = ActionOutcome(action, False, stateBefore, stateAfter)
                    outcomes.append(outcome)
                    return MissionOutcome(False, outcomes)

                # dispatch
                schema.dispatch(action.getValues())
                print('Doing: {}'.format(action.getSchemaName()))

                # loop until postconditions are satisfied, or an invariant is violated
                while True:

                    # check for invariant violations
                    (satisfied, violations) = \
                        schema.satisfiedInvariants(self.__variables, action)
                    if not satisfied:
                        stateAfter = self.getInternalState()
                        outcome = ActionOutcome(action, False, stateBefore, stateAfter)
                        outcomes.append(outcome)
                        return MissionOutcome(False, outcomes)

                    # check if postconditions are satisfied
                    (satisfied, violations) = \
                        schema.satisfiedPostConditions(self.__variables, action)
                    if satisfied:
                        stateAfter = self.getInternalState()
                        outcome = ActionOutcome(action, False, stateBefore, stateAfter)
                        outcomes.append(outcome)
                        return MissionOutcome(True, outcomes)

                    time.sleep(0.5) # TODO: parameterise

                    # TODO: enforce a time-out!

        finally:
            self.tearDown(mission)


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


class ActionSchema(object):
    """
    Action schemas are responsible for describing the kinds of actions that
    can be performed within a given system. Action schemas describe actions
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """

    def __init__(self, name, parameters, preconditions, invariants, postconditions,
        estimators):
        """
        Constructs an ActionSchema object.

        :param  name            name of the action schema
        :param  parameters      a list of the parameters for this action schema
        :param  preconditions   predicates that must be met before the action
                                can be executed.
        :param  invariants      predicates that should be met at all times during
                                the execution of an action.
        :param  postconditions  predicates that must be met after the action is
                                completed.
        :param  estimator       a list of state estimators.
        """
        assert (isinstance(name, str) and not name is None)
        assert (len(name) > 0)
        assert (isinstance(parameters, list) and not parameters is None)
        assert (isinstance(preconditions, list) and not preconditions is None)
        assert (isinstance(postconditions, list) and not postconditions is None)
        assert (isinstance(invariants, list) and not invariants is None)
        assert (isinstance(estimators, list) and not estimators is None)

        self.__name           = name
        self.__parameters     = parameters
        self.__preconditions  = preconditions
        self.__invariants     = invariants
        self.__postconditions = postconditions
        self.__estimators     = estimators


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


    def getParameters(self):
        """
        Returns the parameters being hold for the current action schema. This is
        used to generate actions
        """
        return copy.deepcopy(self.__parameters)


    def getPreconditions(self):
        """
        Returns the preconditions being hold for the current action schema. This
        is used to generate and validate actions.
        """
        return copy.deepcopy(self.__preconditions)


    def satisfiedPostConditions(self, action, currentState, env):
        """
        Checks that the postconditions are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the postconditions that were not met (if any).

        :param  action              the action that is to be executed.
        :param  currentState        the state of the system immediately prior to
                                    the execution of the action.
        :param  env                 the environment in which the action will be
                                    executed.
        """
        #print 'Doing postconditions. Action: {}'.format(parameters.getKind())

        postconditionsFailed = []
        success = True
        for postcondition in self.__postconditions:
            if not postcondition.check(action, currentState, env):
                postconditionsFailed.append(postcondition.getName())
                success = False
        return (success, postconditionsFailed)


    def satisfiedPreconditions(self, action, currentState, env):
        """
        Checks that the preconditions are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the preconditions that were not met (if any).

        :param  action              the action that is to be executed.
        :param  currentState        the state of the system immediately prior to
                                    the execution of the action.
        :param  env                 the environment in which the action will be
                                    executed.
        """
        #print 'Doing precondition. Action: {}'.format(parameters.getKind())

        preconditionsFailed = []
        success = True
        for precondition in self.__preconditions:
            if not precondition.check(action, currentState, env):
                preconditionsFailed.append(precondition.getName())
                success = False
        return (success, preconditionsFailed)


    def satisfiedInvariants(self, action, currentState, env):
        """
        Checks that the invariants are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the invariants that were not met (if any).

        :param  action              the action that is to be executed.
        :param  currentState        the state of the system immediately prior to
                                    the execution of the action.
        :param  env                 the environment in which the action will be
                                    executed.
        """
        #print 'Doing invariants. Action: {}'.format(parameters.getKind())
        invariantsFailed    = []
        success             = True
        for invariant in self.__invariants:
            if not invariant.check(action, currentState, env):
                invariantsFailed.append(invariant.getName())
                success = False
        return (success, invariantsFailed)


    def estimateState(self, action, initialState, environment):
        """
        Estimates the resulting system state after executing an action
        belonging to this schema in a given initial state.

        :param  action:         the action for which an outcome should be \
                                estimated.
        :param  initialState:   the initial state of the system, immediately \
                                prior to executing the action.
        :param  environment:    a description of the environment in which the \
                                action should take place.

        :return An estimate of the resulting system state
        """
        values = initialState.getValues()

        for estimator in self.__estimators:
            var = estimator.getVariableName()
            values[var] = estimator.estimate(action, initialState, environment)

        return state.State(values)
