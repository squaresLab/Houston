import state
import branch
import action

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
        actions = [action.Action.fromJSON(a) for a in jsn['actions']]

        return Mission(env, initialState, actions)


    def __init__(self, environment, initialState, actions):
        """
        Constructs a new Mission description.

        :param  environment:    a description of the environment
        :param  internal:       a description of the initial internal state
        :param  external:       a description of the initial external state
        :param  actions:        a list of actions
        """
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


    def isEmpty(self):
        """
        Returns True if this mission contains no actions.
        """
        return self.__actions == []


    def getInitialState(self):
        return self.__initialState


    def getActions(self):
        return self.__actions[:]


    def size(self):
        """
        Returns the number of actions in this mission.
        """
        return len(self.__actions)


    def getExpectedMissionDuration(self, system):
        """
        Returns the expected time that the mission is going to take based on each
        action timeout.
        """
        durationTime = 0.0
        schemas = system.getActionSchemas()
        for a in self.__actions:
            durationTime += schemas[a.getSchemaName()].computeTimeout(a, self.__initialState, self.__environment)
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
        assert('setupTime' in jsn)
        assert('totalTime' in jsn)
        assert(isinstance(jsn['passed'], bool))
        assert(isinstance(jsn['actions'], list))
        assert(isinstance(jsn['setupTime'], float))
        assert(isinstance(jsn['totalTime'], float))
        actions = [action.ActionOutcome.fromJSON(a) for a in jsn['actions']]
        return MissionOutcome(jsn['passed'], actions, jsn['setupTime'], jsn['totalTime'])


    def __init__(self, passed, outcomes, setupTime, totalTime):
        """
        Constructs a MissionOutcome object.

        :param  passed      indicates the success (or failure) of the mission.
                            True if successful, False if not.
        :param  outcomes    a list containing the ActionOutcomes for the
                            each of the actions in the mission.
        """
        self.__passed = passed
        self.__outcomes  = outcomes
        self.__setupTime = setupTime
        self.__totalTime = totalTime


    def toJSON(self):
        """
        Returns a JSON description of the mission outcome.
        """
        return {
            'passed': self.__passed,
            'actions': [outcome.toJSON() for outcome in  self.__outcomes],
            'setupTime': self.__setupTime,
            'totalTime': self.__totalTime
        }


    def __str__(self):
        return str(self.toJSON())


    def __repr__(self):
        return str(self)

    
    def getExecutedPath(self):
        """
        Returns the branch path that was taken by this mission execution.
        """
        return branch.BranchPath([a.getBranchID() for a in self.__outcomes])


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
