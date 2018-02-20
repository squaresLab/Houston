import houston.branch
from houston.state import Environment, State


class Mission(object):
    """
    A mission is represented as a sequence of actions that are carried out in
    a given environment and initial state.
    """

    @staticmethod
    def from_json(jsn):
        """
        Constructs a mission object from a given JSON description.
        """
        from houston.state import State, Environment
        from houston.action import Action

        assert isinstance(jsn, dict)
        assert('environment' in jsn)
        assert('initialState' in jsn)
        assert('actions' in jsn)
        assert isinstance(jsn['actions'], list)

        env = Environment.from_json(jsn['environment'])
        initial_state = State.from_json(jsn['initialState'])
        actions = [Action.from_json(a) for a in jsn['actions']]

        return Mission(env, initial_state, actions)


    def __init__(self, environment, initial_state, actions):
        """
        Constructs a new Mission description.

        :param  environment:    a description of the environment
        :param  internal:       a description of the initial internal state
        :param  external:       a description of the initial external state
        :param  actions:        a list of actions
        """
        from houston.state import State, Environment

        assert isinstance(environment, Environment)
        assert isinstance(initial_state, State)

        self.__environment = environment
        self.__initial_state = initial_state
        self.__actions = actions

    @property
    def environment(self):
        """
        Returns a description of the (initial) state of the environment
        in which this mission should be executed.
        """
        return self.__environment

    def is_empty(self):
        """
        Returns True if this mission contains no actions.
        """
        return self.__actions == []

    @property
    def initial_state(self):
        return self.__initial_state

    @property
    def actions(self):
        return self.__actions[:]

    @property
    def size(self):
        """
        Returns the number of actions in this mission.
        """
        return len(self.__actions)

    def get_expected_duration(self, system):
        """
        Returns the expected time that the mission is going to take based on each
        action timeout.
        """
        duration = 0.0
        schemas = system.schemas
        for a in self.__actions:
            s = schemas[a.schema_name]
            timeout = s.compute_timeout(a, self.initial_state, self.environment)
            duration += timeout
        return duration

    def extended(self, action):
        """
        Returns a variant of this mission with a given action added onto the
        end.
        """
        from houston.action import Action

        assert isinstance(action, Action)
        actions = self.__actions + [action]
        return Mission(self.environment, self.initial_state, actions)

    def to_json(self):
        """
        Returns a JSON description of this mission.
        """
        return {
            'environment': self.environment.to_json(),
            'initialState': self.initial_state.to_json(),
            'actions': [a.to_json() for a in self.__actions]
        }


class MissionOutcome(object):
    """
    Mission outcomes are used to summarise and record the outcome of performing
    a mission.
    """
    @staticmethod
    def from_json(jsn):
        """
        Constructs a MissionOutcome from a JSON description.
        """
        from houston.action import ActionOutcome

        assert isinstance(jsn, dict)
        assert('passed' in jsn)
        assert('actions' in jsn)
        assert('setupTime' in jsn)
        assert('totalTime' in jsn)
        assert(isinstance(jsn['passed'], bool))
        assert(isinstance(jsn['actions'], list))
        assert(isinstance(jsn['setupTime'], float))
        assert(isinstance(jsn['totalTime'], float))
        actions = [ActionOutcome.from_json(a) for a in jsn['actions']]
        return MissionOutcome(jsn['passed'], actions, jsn['setupTime'], jsn['totalTime'])

    def __init__(self, passed, outcomes, setup_time, total_time):
        """
        Constructs a MissionOutcome object.

        :param  passed      indicates the success (or failure) of the mission.
                            True if successful, False if not.
        :param  outcomes    a list containing the ActionOutcomes for the
                            each of the actions in the mission.
        """
        self.__passed = passed
        self.__outcomes  = outcomes
        self.__setup_time = setup_time
        self.__total_time = total_time

    def to_json(self):
        """
        Returns a JSON description of the mission outcome.
        """
        return {
            'passed': self.__passed,
            'actions': [outcome.to_json() for outcome in  self.__outcomes],
            'setupTime': self.__setup_time,
            'totalTime': self.__total_time
        }

    def __str__(self):
        return str(self.to_json())

    def __repr__(self):
        return str(self)

    @property
    def executed_path(self):
        """
        Returns the branch path that was taken by this mission execution.
        """
        from houston.branch import BranchPath
        return BranchPath([a.branch_id for a in self.__outcomes])

    @property
    def end_state(self):
        """
        A description of the state of the system immediately after the
        execution of this mission.
        """
        return self.__outcomes[-1].end_state

    @property
    def start_state(self):
        """
        A description of the state of the system immediately before the
        execution of this mission.
        """
        return self.__outcomes[0].start_state

    @property
    def passed(self):
        return self.__passed

    @property
    def failed(self):
        """
        Returns true if this mission was unsuccessful.
        """
        return not self.passed


class CrashedMissionOutcome(MissionOutcome):
    def __init__(self, total_time):
        super(CrashedMissionOutcome, self).__init__(False, [], 0.0, total_time)

    def to_json(self):
        jsn = super(CrashedMissionOutcome, self).to_json()
        jsn['crashed'] = True
        return jsn


class MissionSuite(object):
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)
        contents = jsn['contents']
        contents = [Mission.from_json(m) for m in contents]
        return MissionSuite(contents)

    def __init__(self, contents):
        assert isinstance(contents, list)
        assert all(isinstance(m, Mission) for m in contents)
        self.__contents = contents

    @property
    def size(self):
        """
        The number of missions within this suite.
        """
        return self.__contents.length()

    @property
    def contents(self):
        """
        The contents of this mission suite.
        """
        return self.__contents[:]

    def __iter__(self):
        for m in self.__contents:
            yield m

    def to_json(self):
        """
        Produces a JSON-ready description of this mission suite.
        """
        contents = [m.to_json() for m in self.__contents]
        jsn = {'contents': contents}
        return jsn
