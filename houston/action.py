__all__ = \
    ['Action', 'ActionSchema', 'Parameter', 'ActionOutcome', 'ActionGenerator']

from typing import List, Dict, Any, Optional, Type, Generic, TypeVar
import random
import logging

import attr

from .configuration import Configuration
from .state import State
from .environment import Environment
from .valueRange import ValueRange

logger = logging.getLogger(__name__)   # type: logging.Logger
logger.setLevel(logging.DEBUG)


@attr.s(frozen=True)
class Action(object):
    kind = attr.ib(type=str)
    values = attr.ib(type=Dict[str, Any], convert=dict)  # FIXME use FrozenDict

    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'Action':
        return Action(jsn['kind'], jsn['parameters'])

    @property
    def schema_name(self) -> str:
        """
        The name of the schema to which this action belongs.
        """
        return self.kind

    def __getitem__(self, param: str) -> Any:
        """
        Returns the value for a specific parameter in this action.
        """
        return self.values[param]

    def to_json(self) -> Dict[str, Any]:
        return {'kind': self.kind,
                'parameters': self.values.copy()}


@attr.s(frozen=True)
class ActionOutcome(object):
    """
    Describes the outcome of a command execution in terms of the state of the
    system before and after the execution.
    """
    action = attr.ib(type=Action)
    successful = attr.ib(type=bool)
    start_state = attr.ib(type=State)
    end_state = attr.ib(type=State)
    time_elapsed = attr.ib(type=float)  # FIXME use time delta

    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'ActionOutcome':
        return ActionOutcome(Action.from_json(jsn['action']),
                             jsn['successful'],
                             State.from_json(jsn['start_state']),
                             State.from_json(jsn['end_state']),
                             jsn['time_elapsed'])

    def to_json(self) -> Dict[str, Any]:
        return {'action': self.__action.to_json(),
                'successful': self.__successful,
                'start_state': self.start_state.to_json(),
                'end_state': self.end_state.to_json(),
                'time_elapsed': self.__time_elapsed}


T = TypeVar('T')


@attr.s(frozen=True)
class Parameter(Generic[T]):
    name = attr.ib(type=str)
    values = attr.ib(type=ValueRange)

    def generate(self, rng: random.Random) -> T:
        """
        Returns a randomly-generated value for this parameter.
        """
        return self.values.sample(rng)

    @property
    def type(self) -> Type[T]:
        """
        The underlying type of this parameter.
        """
        return self.values.type


class ActionSchema(object):
    """
    Action schemas are responsible for describing the kinds of actions that
    can be performed within a given system. Action schemas describe actions
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """
    def __init__(self,
                 name: str,
                 parameters: List[Parameter],
                 branches: 'List[Branch]'
                 ) -> None:
        """
        Constructs an ActionSchema object.

        Parameters:
            name: name of the action schema.
            parameters: a list of the parameters for this action schema.
            branches: a list of the possible outcomes for actions belonging to
                this schema.
        """
        from houston.branch import Branch  # FIXME this is awful

        assert len(name) > 0
        assert len(branches) > 0

        # unique branch names
        assert (len(set(b.name for b in branches)) == len(branches))

        self.__name = name
        self.__parameters = parameters
        self.__branches = branches

    @property
    def name(self) -> str:
        return self.__name

    @property
    def branches(self) -> List['Branch']:
        """
        A list of the branches for this action schema.
        """
        return self.__branches[:]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment,
                 configuration: Configuration
                 ) -> None:
        """
        Responsible for invoking an action belonging to this schema.

        Args:
            sandbox: the sandbox for the system under test.
            action: the action that is to be dispatched.
            state: the state of the system immediately prior to the
                call to this method
            environment (Environment): a description of the environment in
                which the action is being performed
        """
        raise NotImplementedError

    def timeout(self,
                action: Action,
                state: State,
                environment: Environment,
                config: Configuration
                ) -> float:
        """
        Responsible for calculating the maximum time that a given action
        should take to finish its execution.

        Parameters:
            action: the action.
            state: the state of the system prior to the execution of the
                action.
            environment: the state of the environment prior to the execution
                of the action.

        Returns:
            Maximum length of time (in seconds) that the action may take to
            complete its execution.
        """
        branch = self.resolve_branch(action, state, environment, config)
        return branch.timeout(action, state, environment, config)

    # FIXME replace with frozenset
    @property
    def parameters(self) -> List[Parameter]:
        return self.__parameters[:]

    def resolve_branch(self,
                       action: Action,
                       state: State,
                       environment: Environment,
                       config: Configuration
                       ) -> 'Branch':
        """
        Returns the branch of this action schema that will be taken for a
        given action, state, and environment.
        """
        for b in self.__branches:
            if b.precondition(action, state, environment, config):
                return b
        raise Exception("failed to resolve branch")

    def generate(self, rng: random.Random) -> Action:
        """
        Randomly generates an action belonging to this schema.
        """
        assert (isinstance(rng, random.Random) and rng is not None)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        return Action(self.name, values)


class ActionGenerator(object):
    def __init__(self,
                 schema_name: str,
                 parameters: Optional[List[Parameter]] = None
                 ) -> None:
        """
        Constructs a new action generator.

        Parameters:
            schema_name: the name of the schema used by the actions produced
                by this generator.
            parameters: a list of parameters to this generator.
        """
        self.__schema_name = schema_name
        self.__parameters = parameters if parameters else []

    def construct_with_state(self,
                             state: State,
                             env: Environment,
                             config: Configuration,
                             values: Any  # FIXME
                             ) -> Action:
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError

    def construct_without_state(self,
                                env: Environment,
                                config: Configuration,
                                values: Any  # FIXME
                                ) -> Action:
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        Returns:
            A dictionary of arguments for the generated action
        """
        raise NotImplementedError

    @property
    def schema_name(self) -> str:
        """
        The name of the schema to which actions generated by this
        generator belong.
        """
        return self.__schema_name

    def generate_action_with_state(self,
                                   state: State,
                                   env: Environment,
                                   config: Configuration,
                                   rng: random.Random
                                   ) -> Action:
        values = {p.name: p.generate(rng) for p in self.__parameters}
        values = self.construct_with_state(state, env, config, values)
        return Action(self.__schema_name, values)

    def generate_action_without_state(self,
                                      env: Environment,
                                      config: Configuration,
                                      rng: random.Random,
                                      ) -> Action:
        assert isinstance(rng, random.Random)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        values = self.construct_without_state(system, env, config, values)
        return Action(self.__schema_name, values)
