import thread
import time
import copy
import json

class System(object):
    """
    Description of System.

    TODO: where are external state parameters?
    """


    def __init__(self, identifier, variables, schemas):
        """
        Constructs a new System.

        :param  identifier: a unique string identifier (i.e., a name) for this\
                            system
        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
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
        assert(self.installed())
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


    def getInternalState(self):
        """
        Returns a description of the current internal state of the system.

        TODO: ensure that the system is actually running!
        """
        assert(self.installed())
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return InternalState(vals)


    def getActionSchemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)

    
    def generateMissionContext(self, args):
        # TODO: stub!
        pass


class State(object):
    """
    Describes the internal or external state of the system in terms of its
    internal or external variables.
    """

    def __init__(self, values):
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """
        self.__values = copy.copy(values)


    def read(variable):
        """
        Returns the value for a given state variable
        """
        return self.__values[variable]


    def dump(self):
        """
        Prints this state to the standard output.
        """
        for variable in self.__values:
            print('Variable: {} - State: {}'.format(variable, self.read(variable)))


    def toJSON(self):
        """
        Returns a JSON description of this state.
        """
        return {
            'variables': copy.copy(self.__values)
        }


    def __str__(self):
        return str(self.toJSON())


    def __repr__(self):
        return str(self)


class InternalState(State):
    """
    Describes the state of the system in terms of its internal state
    variables.
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an internal state description from a JSON object
        """
        assert('variables' in jsn)
        assert(isinstance(jsn['variables'], dict))
        return InternalState(jsn['variables'])

class ExternalState(State):
    """
    Describes the state of the system in terms of its external state
    variables.
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an external state description from a JSON object
        """
        assert('variables' in jsn)
        assert(isinstance(jsn['variables'], dict))
        return ExternalState(jsn['variables'])


class StateVariable(object):

    def __init__(self, name, getter):
        """
        Constructs a new state variable

        :param  name:   the name of this variable
        :param  type:   the type of this variable
        :param  getter: a lambda function, used to obtain the value of this variable
        """
        self.__name = name
        self.__getter = getter


    """
    Returns the name of this system variable
    """
    def name(self):
        return self.__name


    """
    Inspects the current state of this system variable
    """
    def read(self):
        return self.__getter()


class InternalStateVariable(StateVariable):
    """
    Internal variables describe the internal state of a given system.
    (i.e., they represent a system's knowledge of itself and its surroundings.)
    A user-provided lambda function is used to inspect the value of the state
    variable at any given time.
    """

    def __init__(self, name, getter):
        super(InternalStateVariable, self).__init__(name, getter)


class Environment(object):
    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a description of an environment from its JSON description
        """
        assert('variables' in jsn)
        assert(isinstance(jsn['variables'], dict))
        return Environment(jsn['variables'])

    """
    Holds a description of an environment in which a mission should be conducted.
    """

    def __init__(self, values):
        """
        Constructs a description of a mission environment.

        :param  values: a dictionary of environment variable values, indexed
                        by the name of those variables.
        """
        self.__values = copy.copy(values)


    def read(self, variable):
        """
        Returns the value of a given environment variable.
        """
        return self.__values[variable]


    def toJSON(self):
        """
        Returns this environment description as a JSON object (i.e., a dict)
        """
        return {
            'variables': copy.copy(self.__values)
        }


class ActionSchema(object):
    """
    Action schemas are responsible for describing the kinds of actions that
    can be performed within a given system. Action schemas describe actions
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """

    def __init__(self, name, parameters, preconditions, invariants, postconditions):
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
        """
        assert(isinstance(name, str) and not name is None)
        assert(len(name) > 0)
        assert(isinstance(parameters, list) and not parameters is None)
        assert(isinstance(preconditions, list) and not preconditions is None)
        assert(isinstance(postconditions, list) and not postconditions is None)
        assert(isinstance(invariants, list) and not invariants is None)

        self.__name           = name
        self.__parameters     = parameters
        self.__preconditions  = preconditions
        self.__invariants     = invariants
        self.__postconditions = postconditions

    
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


    def satisfiedPostConditions(self, systemVariables, parameters):
        """
        Checks that the postconditions are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the postconditions that were not met (if any).

        :param  systemVariables     the system variables.
        :param  parameters          parameters of the action that is being executed.
        """
        #print 'Doing postconditions. Action: {}'.format(parameters.getKind())
        postconditionsFailed = []
        success               = True
        for postcondition in self.__postconditions:
            if not postcondition.check(systemVariables, parameters.getValues()):
                postconditionsFailed.append(postcondition.getName())
                success = False

        return (success, postconditionsFailed)


    def satisfiedPreconditions(self, systemVariables, parameters):
        """
        Checks that the preconditions are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the preconditions that were not met (if any).

        :param  systemVariables     the system variables.
        :param  parameters          parameters of the action that is about to be
                                    dispatched.
        """
        #print 'Doing precondition. Action: {}'.format(parameters.getKind())
        preconditionsFailed = []
        success              = True
        for precondition in self.__preconditions:
            if not precondition.check(systemVariables, parameters.getValues()):
                preconditionsFailed.append(precondition.getName())
                success = False
        return (success, preconditionsFailed)


    def satisfiedInvariants(self, systemVariables, parameters):
        """
        Checks that the invariants are met. Returns a tuple, with a boolean
        holding the success or failure of the check, and a list with the name of
        the invariants that were not met (if any).

        :param  systemVariables     the system variables.
        :param  parameters          parameters of the action that is about to be
                                    dispatched or that is currently being executed.
        """
        #print 'Doing invariants. Action: {}'.format(parameters.getKind())
        invariantsFailed    = []
        success             = True
        for invariant in self.__invariants:
            if not invariant.check(systemVariables, parameters.getValues()):
                invariantsFailed.append(invariant.getName())
                success = False
        return (success, invariantsFailed)
