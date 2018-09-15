__all__ = ['Mission', 'MissionOutcome', 'CrashedMissionOutcome',
           'MissionSuite']

from typing import Dict, Any, List, Iterator

import attr

from .configuration import Configuration
from .action import Action, ActionOutcome
from .state import State
from .environment import Environment


@attr.s(frozen=True)
class Mission(object):
    """
    A mission is represented as a sequence of actions that are carried out in
    a given environment and initial state.
    """
    configuration = attr.ib(type=Configuration)
    environment = attr.ib(type=Environment)
    initial_state = attr.ib(type=State)
    actions = attr.ib(type=List[Action])  # FIXME

    @staticmethod
    def from_dict(jsn: Dict[str, Any]) -> 'Mission':
        env = Environment.from_json(jsn['environment'])
        config = Configuration.from_json(jsn['configuration'])
        initial_state = State.from_json(jsn['initial_state'])
        actions = [Action.from_json(a) for a in jsn['actions']]
        return Mission(config, env, initial_state, actions)

    def is_empty(self) -> bool:
        """
        Returns True if this mission contains no actions.
        """
        return self.actions == []

    def __iter__(self) -> Iterator[Action]:
        """
        Returns an iterator over the actions contained in this mission.
        """
        yield from self.actions

    @property
    def size(self) -> int:
        """
        The number of actions in this mission.
        """
        return len(self.actions)

    def extended(self, action: Action) -> 'Mission':
        """
        Returns a variant of this mission with a given action added onto the
        end.
        """
        actions = self.actions + [action]
        return Mission(self.environment, self.initial_state, actions)

    def to_dict(self) -> Dict[str, Any]:
        return {
            'configuration': self.configuration.to_json(),
            'environment': self.environment.to_json(),
            'initial_state': self.initial_state.to_json(),
            'actions': [a.to_json() for a in self.__actions]}


@attr.s(frozen=True)
class MissionOutcome(object):
    """
    Mission outcomes are used to summarise and record the outcome of performing
    a mission.
    """
    passed = attr.ib(type=bool)
    outcomes = attr.ib(type=List[ActionOutcome])
    time_setup = attr.ib(type=float)
    time_total = attr.ib(type=float)

    @staticmethod
    def from_dict(dkt: Dict[str, Any]) -> 'MissionOutcome':
        actions = [ActionOutcome.from_json(a) for a in jsn['actions']]
        return MissionOutcome(dkt['passed'],
                              actions,
                              dkt['time_setup'],
                              dkt['time_total'])

    def to_dict(self) -> Dict[str, Any]:
        return {'passed': self.passed,
                'actions': [outcome.to_json() for outcome in self.outcomes],
                'time_setup': self.time_setup,
                'time_total': self.time_total}

    # FIXME what is this for?
    def to_test_outcome_json(self, code: int) -> Dict[str, Any]:
        """
        Returns a JSON description of mission outcome in the serialized
        format of a TestOutcome object in BugZoo.
        """
        response = {
            'code': code,
            'duration': self.time_total,
            'output': json.dump([o.to_json() for o in self.outcomes])}
        return {'passed': self.__passed,
                'response': response}

    def __repr__(self) -> str:
        outcomes = [repr(o) for o in self.outcomes]  # type: List[str]
        s_passed = "passed={}".format(repr(self.passed))
        s_time_setup = "time_setup={:.3f}".format(self.time_setup)
        s_time_total = "time_total={:.3f}".format(self.time_total)
        s_outcomes = "outcomes={}".format(repr(outcomes))
        s = '; '.join([s_passed, s_time_setup, s_time_total, s_outcomes])
        s = "MissionOutcome({})".format(s)
        return s

    @property
    def end_state(self) -> State:
        """
        A description of the state of the system immediately after the
        execution of this mission.
        """
        return self.outcomes[-1].end_state

    @property
    def start_state(self) -> State:
        """
        A description of the state of the system immediately before the
        execution of this mission.
        """
        return self.outcomes[0].start_state


class CrashedMissionOutcome(MissionOutcome):
    def __init__(self, total_time: float) -> None:
        super().__init__(False, [], 0.0, total_time)

    def to_dict(self):
        dkt = super().to_dict()
        dkt['crashed'] = True
        return dkt


class MissionSuite(object):
    @staticmethod
    def from_dict(dkt: Dict[str, Any]) -> 'MissionSuite':
        contents = [Mission.from_dict(m) for m in dkt['contents']]
        return MissionSuite(contents)

    def __init__(self, contents: List[Mission]) -> None:
        self.__contents = contents

    @property
    def size(self) -> int:
        return self.__contents.length()

    def __iter__(self):
        yield from self.__contents

    def to_dict(self) -> Dict[str, Any]:
        contents = [m.to_dict() for m in self.__contents]
        dkt = {'contents': contents}
        return dkt
