from typing import Dict, Any, List, Iterator

from .action import Action, ActionOutcome
from .state import Environment, State
from .branch import BranchPath


class Mission(object):
    """
    A mission is represented as a sequence of actions that are carried out in
    a given environment and initial state.
    """
    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'Mission':
        """
        Constructs a mission object from a given JSON description.
        """
        env = Environment.from_json(jsn['environment'])
        initial_state = State.from_json(jsn['initial_state'])
        actions = [Action.from_json(a) for a in jsn['actions']]
        return Mission(env, initial_state, actions)

    def __init__(self,
                 environment: Environment,
                 initial_state: State,
                 actions: List[Action]
                 ) -> None:
        """
        Constructs a new Mission description.

        Parameters:
            environment: a description of the environment.
            initial_state: a description of the initial state.
            external: a description of the initial external state.
            actions: a list of actions.
        """
        self.__environment = environment
        self.__initial_state = initial_state
        self.__actions = actions

    @property
    def environment(self) -> Environment:
        """
        A description of the (initial) state of the environment in which
        this mission should be executed.
        """
        return self.__environment

    def is_empty(self) -> bool:
        """
        Returns True if this mission contains no actions.
        """
        return self.__actions == []

    @property
    def initial_state(self) -> State:
        return self.__initial_state

    def __iter__(self) -> Iterator[Action]:
        """
        Returns an iterator over the actions contained in this mission.
        """
        yield from self.__actions

    # FIXME prefer iterator
    @property
    def actions(self) -> List[Action]:
        return self.__actions[:]

    @property
    def size(self) -> int:
        """
        The number of actions in this mission.
        """
        return len(self.__actions)

    def get_expected_duration(self, system: 'System') -> float:
        """
        Returns the expected time taken to complete the mission, computed as
        the sum of the timeouts for its constituent actions.
        """
        duration = 0.0
        schemas = system.schemas
        for action in self.__actions:
            schema = schemas[action.schema_name]
            timeout = schema.compute_timeout(action,
                                             self.initial_state,
                                             self.environment)
            duration += timeout
        return duration

    def extended(self, action: Action) -> 'Mission':
        """
        Returns a variant of this mission with a given action added onto the
        end.
        """
        actions = self.__actions + [action]
        return Mission(self.environment, self.initial_state, actions)

    def to_json(self) -> Dict[str, Any]:
        return {
            'environment': self.environment.to_json(),
            'initial_state': self.initial_state.to_json(),
            'actions': [a.to_json() for a in self.__actions]}


class MissionOutcome(object):
    """
    Mission outcomes are used to summarise and record the outcome of performing
    a mission.
    """
    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'MissionOutcome':
        """
        Constructs a MissionOutcome from a JSON description.
        """
        actions = [ActionOutcome.from_json(a) for a in jsn['actions']]
        return MissionOutcome(jsn['passed'],
                              actions,
                              jsn['setup_time'],
                              jsn['total_time'])

    def __init__(self,
                 passed: bool,
                 outcomes: List[ActionOutcome],
                 setup_time: float,
                 total_time: float
                 ) -> None:
        """
        Constructs a MissionOutcome object.

        Parameters:
            passed: indicates the success (or failure) of the mission.
                True if mission was successful, else False.
            outcomes: the outcome of each action within this mission,
                given in sequence.
            setup_time: the number of seconds to prepare the system before
                beginning the mission.
            total_time: the number of seconds to complete the mission,
                including the time taken to perform setup.
        """
        self.__passed = passed
        self.__outcomes = outcomes
        self.__setup_time = setup_time
        self.__total_time = total_time

    def to_json(self) -> Dict[str, Any]:
        return {
            'passed': self.__passed,
            'actions': [outcome.to_json() for outcome in self.__outcomes],
            'setup_time': self.__setup_time,
            'total_time': self.__total_time}

    # FIXME what is this for?
    def to_test_outcome_json(self, code: int) -> Dict[str, Any]:
        """
        Returns a JSON description of mission outcome in the serialized
        format of a TestOutcome object in BugZoo.
        """
        response = {
            'code': code,
            'duration': self.__total_time,
            'output': json.dump([o.to_json() for o in self.__outcomes])}
        return {'passed': self.__passed,
                'response': response}

    def __repr__(self) -> str:
        outcomes = [repr(o) for o in self.__outcomes]  # type: List[str]
        s_passed = "passed={}".format(repr(self.__passed))
        s_time_setup = "setup_time={:.3f}".format(self.__setup_time)
        s_time_total = "total_time={:.3f}".format(self.__total_time)
        s_outcomes = "outcomes={}".format(repr(outcomes))
        s = '; '.join([s_passed, s_time_setup, s_time_total, s_outcomes])
        s = "MissionOutcome({})".format(s)
        return s

    @property
    def executed_path(self) -> BranchPath:
        """
        Returns the branch path that was taken by this mission execution.
        """
        return BranchPath([o.branch_id for o in self.__outcomes])

    @property
    def end_state(self) -> State:
        """
        A description of the state of the system immediately after the
        execution of this mission.
        """
        return self.__outcomes[-1].end_state

    @property
    def start_state(self) -> State:
        """
        A description of the state of the system immediately before the
        execution of this mission.
        """
        return self.__outcomes[0].start_state

    @property
    def passed(self) -> bool:
        return self.__passed

    @property
    def failed(self) -> bool:
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
