import thread
import time
import copy
import json

class System(object):
    """
    Description of System.
    """


    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


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
        Executes the mission. Returns mission outcome
        """
        self.setUp(mission)
        outcomes = []
        missionPassed = True
        for action in mission.getActions():
            actionKind   = action.getKind()
            actionSchema = self.__schemas[actionKind]
            outcome = ActionOutcome(actionKind, self.getInternalState())
            # check for invariants

            result = actionSchema.satisfiedInvariants(self.__variables, action)
            if not result[0]:
                outcome.setActionReturn(False, 'Invariants : {}'.format(result[1]))
                outcome.setPostActionSystemState(self.getInternalState())
                outcomes.append(outcome)
                missionPassed = False
                break
            # check for preconditions
            result =  actionSchema.satisfiedPreconditions(self.__variables, action)
            if not result[0]:
                outcome.setActionReturn(False, 'Preconditions : {}'.format(result[1]))
                outcome.setPostActionSystemState(self.getInternalState())
                outcomes.append(outcome)
                missionPassed = False
                break
            # dispatch
            actionSchema.dispatch(action.getValues())
            print 'Doing: {}'.format(actionKind)
            # start looping till action completed or invariant violated
            while not actionSchema.satisfiedPostConditions(self.__variables, action)[0]:
                time.sleep(0.5)
                result = actionSchema.satisfiedInvariants(self.__variables, action)
                if not result[0]:
                    outcome.setActionReturn(False, 'Invariants : {}'.format(result[1]))
                    outcome.setPostActionSystemState(self.getInternalState())
                    outcomes.append(outcome)
                    missionPassed = False
                    break
            outcome.setActionReturn(True, 'Postconditions')
            outcome.setPostActionSystemState(self.getInternalState())
            outcomes.append(outcome)

        return MissionOutcome(missionPassed, outcomes)


    def getInternalState(self):
        """
        Returns a description of the current internal state of the system.

        TODO: ensure that the system is actually running!
        """
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return InternalState(vals)

    def getActionSchemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)


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

    def __init__(self, name, parameters, precondition, invariants, postconditions):
        """
        Constructs an ActionSchema object.

        :param  name            name of the action
        :param  parameters      parameters of the action
        :param  precondition    predicates that must be met before the action
                                can be executed.
        :param  invariants      predicates that should be met at all times during
                                the execution of an action.
        :param  postconditions  predicates that must be met after the action is
                                completed.
        """
        self.__name           = name
        self.__parameters     = parameters
        self.__preconditions   = precondition
        self.__invariants     = invariants
        self.__postconditions = postconditions


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


class Parameter(object):
    """
    Parameter holds the values necessary for the completion of an action.
    """

    def __init__(self, typ, value, description):
        """
        Constructs a Parameter object.

        :param  typ                 type of parameter. Basically the name of the
                                    parameter. (ex. altitude, longitude..)
        :param  value               the actual value that the parameter carries.
        :param  description         quick description of the parameter
        """
        self.__type = typ
        self.__value = value
        self._description = description


    def getType(self):
        """
        Returns the type of the parameter (Basically the name of the parameter)
        """
        return self.__type


    def getValue(self):
        """
        Returns the value of the parameter.
        """
        return self.__value
