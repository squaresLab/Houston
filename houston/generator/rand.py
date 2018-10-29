from typing import Type, Dict, Callable, Optional

from .base import MissionGenerator
from ..mission import Mission
from ..system import System
from ..state import State
from ..environment import Environment
from ..configuration import Configuration
from ..command import Command


class RandomMissionGenerator(MissionGenerator):
    def __init__(self,
                 system: Type[System],
                 initial_state: State,
                 env: Environment,
                 config: Configuration,
                 threads: int = 1,
                 command_generators: Optional[Dict[str, Callable]] = None,
                 max_num_commands: int = 10
                 ) -> None:
        super().__init__(system, threads, command_generators, max_num_commands)
        self.__initial_state = initial_state
        self.__env = env
        self.__configuration = config

    @property
    def initial_state(self):
        """
        The initial state used by all missions produced by this generator.
        """
        return self.__initial_state

    @property
    def env(self):
        """
        The environment used by all missions produced by this generator.
        """
        return self.__env

    def generate_command(self, command_class: Type[Command]) -> Command:
        generator = self.command_generator(command_class)
        if generator is None:
            return command_class.generate(self.rng)
        # g = generator.generate_action_without_state
        # return g(self.system, self.__env, self.rng)
        return g(self.rng)

    def generate_mission(self):
        command_classes = list(self.system.commands.values())
        commands = []
        for _ in range(self.rng.randint(1, self.max_num_commands)):
            command_class = self.rng.choice(command_classes)
            commands.append(self.generate_command(command_class))
        return Mission(self.__configuration,
                       self.__env,
                       self.__initial_state,
                       commands,
                       self.system)
