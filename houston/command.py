__all__ = \
    ['Command', 'CommandSchema', 'Parameter', 'CommandOutcome']

from typing import List, Dict, Any, Optional, Type, Generic, TypeVar
import random
import logging

import attr

from .specification import Specification
from .configuration import Configuration
from .state import State
from .environment import Environment
from .valueRange import ValueRange

logger = logging.getLogger(__name__)   # type: logging.Logger
logger.setLevel(logging.DEBUG)


@attr.s(frozen=True)
class Command(object):
    kind = attr.ib(type=str)
    values = attr.ib(type=Dict[str, Any], convert=dict)  # FIXME use FrozenDict

    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'Command':
        return Command(jsn['kind'], jsn['parameters'])

    @property
    def schema_name(self) -> str:
        """
        The name of the schema to which this command belongs.
        """
        return self.kind

    def __getitem__(self, param: str) -> Any:
        """
        Returns the value for a specific parameter in this command.
        """
        return self.values[param]

    def to_json(self) -> Dict[str, Any]:
        return {'kind': self.kind,
                'parameters': self.values.copy()}


@attr.s(frozen=True)
class CommandOutcome(object):
    """
    Describes the outcome of a command execution in terms of the state of the
    system before and after the execution.
    """
    command = attr.ib(type=Command)
    successful = attr.ib(type=bool)
    start_state = attr.ib(type=State)
    end_state = attr.ib(type=State)
    time_elapsed = attr.ib(type=float)  # FIXME use time delta

    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'CommandOutcome':
        return CommandOutcome(Command.from_json(jsn['command']),
                              jsn['successful'],
                              State.from_json(jsn['start_state']),
                              State.from_json(jsn['end_state']),
                              jsn['time_elapsed'])

    def to_json(self) -> Dict[str, Any]:
        return {'command': self.__command.to_json(),
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


class CommandSchema(object):
    """
    Command schemas are responsible for describing the kinds of commands that
    can be performed within a given system. Command schemas describe commands
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """
    def __init__(self,
                 name: str,
                 parameters: List[Parameter],
                 specs: List[Specification]
                 ) -> None:
        """
        Constructs an CommandSchema object.

        Parameters:
            name: name of the command schema.
            parameters: a list of the parameters for this command schema.
            branches: a list of the possible outcomes for commands belonging to
                this schema.
        """
        assert len(name) > 0
        assert len(specs) > 0

        # unique specification names
        assert len(set(s.name for s in specs)) == len(specs)

        self.__name = name
        self.__parameters = parameters
        self.__specifications = specs

    @property
    def name(self) -> str:
        return self.__name

    @property
    def specifications(self) -> List[Specification]:
        """
        A list of the specifications for this command schema.
        """
        return self.__specifications[:]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 command: Command,
                 state: State,
                 environment: Environment,
                 configuration: Configuration
                 ) -> None:
        """
        Responsible for invoking an command belonging to this schema.

        Args:
            sandbox: the sandbox for the system under test.
            command: the command that is to be dispatched.
            state: the state of the system immediately prior to the
                call to this method
            environment (Environment): a description of the environment in
                which the command is being performed
        """
        raise NotImplementedError

    def timeout(self,
                command: Command,
                state: State,
                environment: Environment,
                config: Configuration
                ) -> float:
        """
        Responsible for calculating the maximum time that a given command
        should take to finish its execution.

        Parameters:
            command: the command.
            state: the state of the system prior to the execution of the
                command.
            environment: the state of the environment prior to the execution
                of the command.

        Returns:
            Maximum length of time (in seconds) that the command may take to
            complete its execution.
        """
        spec = self.resolve(command, state, environment, config)
        return spec.timeout(command, state, environment, config)

    # FIXME replace with frozenset
    @property
    def parameters(self) -> List[Parameter]:
        return self.__parameters[:]

    def resolve(self,
                command: Command,
                state: State,
                environment: Environment,
                config: Configuration
                ) -> Specification:
        """
        Returns the specification of this command schema that will be taken for
        a given command, state, and environment.
        """
        for spec in self.__specifications:
            if spec.precondition(command, state, environment, config):
                return spec
        raise Exception("failed to resolve specification")
