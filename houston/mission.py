import copy
import system

class Mission(object):
    """
    A mission is represented as a sequence of actions that are carried out in
    a given environment and initial state.
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a mission object from a given JSON description.
        """
        assert(isinstance(jsn, dict) and not jsn is None)
        assert('environment' in jsn)
        assert('internal' in jsn)
        assert('external' in jsn)
        assert('actions' in jsn)
        assert(isinstance(jsn['actions'], list))

        env = system.Environment.fromJSON(jsn['environment'])
        internal = system.InternalState.fromJSON(jsn['internal'])
        external = system.ExternalState.fromJSON(jsn['external'])
        actions = [Action.fromJSON(action) for action in jsn['actions']]

        return Mission(env, internal, external, actions)


    def __init__(self, environment, internal, external, actions):
        """
        Constructs a new Mission description.

        :param  environment:    a description of the environment
        :param  internal:       a description of the initial internal state
        :param  external:       a description of the initial external state
        :param  actions:        a list of actions
        """
        assert(actions != [])
        assert(isinstance(environment, system.Environment) and not environment is None)
        assert(isinstance(internal, system.InternalState) and not internal is None)
        assert(isinstance(external, system.ExternalState) and not external is None)

        self.__environment = environment
        self.__internal = internal
        self.__external = external
        self.__actions = actions


    def getEnvironment(self):
        """
        Returns a description of the (initial) state of the environment
        in which this mission should be executed.
        """
        return self.__environment


    def getInitialInternalState(self):
        return self.__internal


    def getInitialExternalState(self):
        return self.__external


    def getActions(self):
        return copy.copy(self.__actions)


    def toJSON(self):
        """
        Returns a JSON description of this mission.
        """
        return {
            'environment': self.__environment.toJSON(),
            'internal': self.__internal.toJSON(),
            'external': self.__external.toJSON(),
            'actions': [a.toJSON() for a in self.__actions]
        }


#class MissionContext(object):
#    """
#    Mission contexts are used to describe a context in which a mission should
#    take place. Context is given by the initial state of the environment, and
#    the initial values of the internal and external system variables.
#    """


class MissionOutcome(object):
    """
    Mission outcomes are used to summarise and record the outcome of performing
    a mission.
    """
    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a MissionOutcome from a JSON description.
        """
        assert(isinstance(jsn, dict) and not jsn is None)
        assert('passed' in jsn)
        assert('actions' in jsn)
        assert(isinstance(jsn['passed'], bool))
        assert(isinstance(jsn['actions'], list))
        actions = [ActionOutcome.fromJSON(a) for a in jsn['actions']]
        return MissionOutcome(jsn['passed'], actions)


    def __init__(self, passed, outcomes):
        """
        Constructs a MissionOutcome object.

        :param  passed      indicates the success (or failure) of the mission.
                            True if successful, False if not.
        :param  outcomes    a list containing the ActionOutcomes for the
                            each of the actions in the mission.
        """
        self.__passed = passed
        self.__outcomes  = outcomes


    def toJSON(self):
        """
        Returns a JSON description of the mission outcome.
        """
        return {
            'passed': self.__passed,
            'actions': [outcome.toJSON() for outcome in  self.__outcomes]
        }


    def __str__(self):
        return str(self.toJSON())


    def __repr__(self):
        return str(self)


class ActionOutcome(object):
    """
    Used to describe the outcome of an action execution in terms of system state.
    """
    def __init__(self, action, successful, stateBefore, stateAfter):
        """
        Constructs a ActionOutcome.

        :param  action      the action that was performed
        :param  stateBefore the state of the system immediately prior to execution
        :param  stateAfter  the state of the system immediately after execution
        """
        assert(isinstance(action, Action) and not action is None)
        assert(isinstance(successful, bool) and not successful is None)

        self.__action = action
        self.__successful = successful
        self.__stateBefore = stateBefore # TODO: type checking
        self.__stateAfter = stateAfter # TODO: type checking


    def toJSON(self):
        return {
            'action': self.__action,
            'successful': self.__successful,
            'stateBefore': self.__stateBefore,
            'stateAfter': self.__stateAfter
        }


class Action(object):
    """
    Description of the concept of "Actions".
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an Action object from its JSON description.
        """
        assert(isinstance(jsn, dict) and not jsn is None)
        assert('kind' in jsn)
        assert('parameters' in jsn)
        return Action(jsn['kind'], jsn['parameters'])


    def __init__(self, kind, values):
        """
        Constructs an Action description.

        :param  kind    the name of the schema to which the action belongs
        :param  values  a dictionary of parameter values for the action
        """
        assert(isinstance(kind, str) and not kind is None)
        assert(isinstance(values, dict) and not values is None)
        self.__kind = kind
        self.__values = copy.copy(values)


    def getSchemaName(self):
        """
        Returns the name of the schema to which this action belongs.
        """
        return self.__kind


    def getValue(self, value):
        """
        Returns an value of a specific parameter for this action.
        """
        return self.__values[value]


    def getValues(self):
        """
        Returns a copy of the parameters for this action.
        """
        return copy.copy(self.__values)


    def toJSON(self):
        """
        Returns a JSON description of this action.
        """
        return {
            'kind': self.__kind,
            'parameters': self.getValues()
        }


class Parameter(object):
    """
    Docstring.
    """

    def __init__(self, name, valueRange, description):
        """
        Constructs a Parameter object.

        :param  name:           the name of this parameter
        :param  valueRange:     the range of possible values for this parameter,\
                                given as a ValueRange object.
        :param  description:    a short description of the parameter
        """
        self.__name = name
        self.__valueRange = valueRange
        self.__description = description


    def getValueRange(self):
        """
        Returns the range of possible values for this parameter.
        """
        return self.__valueRange

    def generate(self):
        """
        Returns a sample (random)
        """
        return self.__valueRange.sample()

    def getType(self):
        """
        Returns the type of this parameter
        """
        return self.__valueRange.getType()


    def getDescription(self):
        """
        Returns a description of this parameter
        """
        return self.__description


    def getName(self):
        """
        Returns the name of this parameter.
        """
        return self.__name
