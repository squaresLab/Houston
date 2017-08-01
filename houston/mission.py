class MissionSet(object):
    """
    A mission set is a sequence of missions.

    @deprecated
    """

    @staticmethod
    def fromFile(fn):
        """
        Loads a set of missions from a file at a specified location.

        :param  fn  The path to the file containing the mission set.

        :returns    The corresponding MissionSet for that file.
        """
        with open(fn, 'r') as f:
            missions = json.load(f)
        assert('testSuite' in missions) # TODO: why is this named 'testSuite'?
        missions = missions['testSuite']

        return MissionSet([Mission.fromJSON(m) for m in missions])


    def __init__(self, missions):
        assert(isinstance(missions, list))
        self.__missions = missions


    def append(self, mission):
        """
        Appends a mission to the mission set.

        :param  mission     mission to append
        """
        self.__missions.append(mission)


    def remove(self, index):
        """
        Removes a mission from a given index.

        :param  index       index of mission to remove.

        :returns    the removed mission
        """
        assert(0 <= index < len(self.__missions))
        return self.__missions.pop(index)


    def getMissionList(self):
        """
        Returns a copy of the missions in a list.
        """
        return copy.deepcopy(self.__missions)


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
        assert('environment' in jsn)
        assert('internal' in jsn)
        assert('external' in jsn)
        assert('actions' in jsn)
        assert(isinstance(jsn['actions'], list))

        env = Environment.fromJSON(jsn['environment'])
        internal = InternalState.fromJSON(jsn['internal'])
        external = ExternalState.fromJSON(jsn['external'])
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
        assert(isinstance(environment, Environment) and not environment is None)
        assert(isinstance(internal, InternalState) and not internal is None)
        assert(isinstance(external, ExternalState) and not external is None)

        self.__environment = environment
        self.__internal = internal
        self.__external = external
        self.__actions = actions

    # TODO: make immutable
    def getEnvironment(self):
        return self.__environment

    # TODO: make immutable
    def getInitialInternalState(self):
        return self.__internal

    # TODO: make immutable
    def getInitialExternalState(self):
        return self.__external

    # TODO: make immutable
    def getActions(self):
        # TODO: returning the original list might be dangerous? We may want to
        #       pass a copy, instead.
        return self.__actions

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

class MissionOutcome(object):

    def __init__(self, passFail, outcomes):
        """
        Constructs a MissionOutcome object.

        :param  passFail    holds the outcome of the missions. True for passed
                            and False for failed.
        :param  outcomes    a list that cointains the ActionOutcomes for the
                            mission.
        """
        self.__passFail  = passFail
        self.__outcomes  = outcomes

    def toJSON(self):
        """
        Returns a JSON description of the mission outcome.
        """
        return {
            'passed': self.__passFail,
            'actions': [outcome.toJSON() for outcome in  self.__outcomes]
        }

    def __str__(self):
        return str(self.toJSON())

    def __repr__(self):
        return str(self)



