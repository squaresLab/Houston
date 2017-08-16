import copy
import system
import state

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
        assert('initialState' in jsn)
        assert('actions' in jsn)
        assert(isinstance(jsn['actions'], list))

        env = state.Environment.fromJSON(jsn['environment'])
        initialState = state.State.fromJSON(jsn['initialState'])
        actions = [Action.fromJSON(action) for action in jsn['actions']]

        return Mission(env, initialState, actions)


    def __init__(self, environment, initialState, actions):
        """
        Constructs a new Mission description.

        :param  environment:    a description of the environment
        :param  internal:       a description of the initial internal state
        :param  external:       a description of the initial external state
        :param  actions:        a list of actions
        """
        # assert(actions != [])
        assert(isinstance(environment, state.Environment) and not environment is None)
        assert(isinstance(initialState, state.State) and not initialState is None)

        self.__environment = environment
        self.__initialState = initialState
        self.__actions = actions


    def getEnvironment(self):
        """
        Returns a description of the (initial) state of the environment
        in which this mission should be executed.
        """
        return self.__environment


    def getInitialState(self):
        return self.__initialState


    def getActions(self):
        return copy.copy(self.__actions)


    def getExpectedMissionDuration(self, system):
        """
        Returns the expected time that the mission is going to take based on each
        action timeout.
        """
        durationTime = 0.0
        schemas = system.getActionSchemas()
        for action in self.__actions:
            durationTime += schemas[action.getSchemaName()].computeTimeout(action, self.__initialState, self.__environment)
        return durationTime


    def toJSON(self):
        """
        Returns a JSON description of this mission.
        """
        return {
            'environment': self.__environment.toJSON(),
            'initialState': self.__initialState.toJSON(),
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


    def getEndState(self):
        """
        Returns a description of the state of the system immediately after the
        execution of this mission.
        """ 
        return self.__outcomes[-1].getEndState()


    def getStartState(self):
        """
        Returns a description of the state of the system immediately before the
        execution of this mission.
        """
        return self.__outcomes[0].getStartState()


    def passed(self):
        """
        :see `successful`
        """
        return self.__passed


    def failed(self):
        """
        Returns true if this mission was unsuccessful.
        """
        return not self.passed()


class ActionOutcome(object):
    @staticmethod
    def fromJSON(jsn):
        """
        TODO
        """
        assert (isinstance(jsn, dict) and not jsn is None)
        assert ('successful' in jsn)
        assert ('action' in jsn)
        assert ('stateBefore' in jsn)
        assert ('stateAfter' in jsn)
        assert ('timeElapsed' in jsn)
        assert (isinstance(jsn['successful'], bool) and not jsn['successful'] is None)

        return ActionOutcome(Action.fromJSON(jsn['action']),
                             jsn['successful'],
                             state.State.fromJSON(jsn['stateBefore']),
                             state.State.fromJSON(jsn['stateAfter']),
                             jsn['timeElapsed'])


    """
    Used to describe the outcome of an action execution in terms of system state.
    """
    def __init__(self, action, successful, stateBefore, stateAfter, timeElapsed):
        """
        Constructs a ActionOutcome.

        :param  action      the action that was performed
        :param  stateBefore the state of the system immediately prior to execution
        :param  stateAfter  the state of the system immediately after execution
        """
        assert (isinstance(action, Action) and not action is None)
        assert (isinstance(successful, bool) and not successful is None)
        assert (isinstance(stateBefore, state.State) and not stateBefore is None)
        assert (isinstance(stateAfter, state.State) and not stateAfter is None)
        assert (isinstance(timeElapsed, float) and not timeElapsed is None)

        self.__action      = action
        self.__successful  = successful
        self.__stateBefore = stateBefore
        self.__stateAfter  = stateAfter
        self.__timeElapsed = timeElapsed


    def toJSON(self):
        """
        Returns a JSON description of this action outcome.
        """
        return {
            'action':       self.__action.toJSON(),
            'successful':   self.__successful,
            'stateBefore':  self.__stateBefore.toJSON(),
            'stateAfter':   self.__stateAfter.toJSON(),
            'timeElapsed':  self.__timeElapsed
        }


    def passed(self):
        """
        :see `successful`
        """
        return self.successful()


    def successful(self):
        """
        Returns true if this action was unsuccessful.
        """
        return self.__successful


    def failed(self):
        """
        Returns true if this action was unsuccessful.
        """
        return not self.__successful


    def getEndState(self):
        """
        Returns a description of the state of the system immediately after the
        execution of this action.
        """
        return self.__stateAfter


    def getStartState(self):
        """
        Returns a description of the state of the system immediately before the
        execution of this action.
        """
        return self.__startBefore


class Action(object):
    """
    Description of the concept of "Actions".
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an Action object from its JSON description.
        """
        assert (isinstance(jsn, dict) and not jsn is None)
        assert ('kind' in jsn)
        assert ('parameters' in jsn)
        return Action(jsn['kind'], jsn['parameters'])


    def __init__(self, kind, values):
        """
        Constructs an Action description.

        :param  kind    the name of the schema to which the action belongs
        :param  values  a dictionary of parameter values for the action
        """
        assert ((isinstance(kind, str) or (isinstance(kind, unicode))) and not kind is None)
        assert (isinstance(values, dict) and not values is None)
        self.__kind = kind
        self.__values = copy.copy(values)


    def getSchemaName(self):
        """
        Returns the name of the schema to which this action belongs.
        """
        return self.__kind


    def read(self, value):
        """
        Returns the value for a specific parameter in this action.
        """
        return self.getValue(value)


    def getValue(self, value):
        """
        Returns the value for a specific parameter in this action.
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

    def __init__(self, name, valueRange, description='N/A'):
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
