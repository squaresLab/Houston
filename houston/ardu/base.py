__all__ = ['BaseSystem']

from typing import List, Type

from bugzoo.core.bug import Bug as Snapshot

from .sandbox import Sandbox
from ..configuration import Configuration
from ..system import System
from ..util import printflush
from ..command import Command
from ..state import Variable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    is_abstract = True

    def __init__(self,
                 snapshot: Snapshot,
                 commands: List[Type[Command]],
                 config: Configuration
                 ) -> None:
        super().__init__(commands, snapshot, config)

    def provision(self) -> Sandbox:
        return Sandbox(self)
