__all__ = ['BaseSystem']

from typing import List

from bugzoo.core.bug import Bug as Snapshot

from .sandbox import Sandbox
from ..configuration import Configuration
from ..system import System
from ..util import printflush
from ..command import CommandSchema
from ..state import Variable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    is_abstract = True

    def __init__(self,
                 snapshot: Snapshot,
                 schemas: List[CommandSchema],
                 config: Configuration
                 ) -> None:
        super().__init__(schemas, snapshot, config)

    def provision(self) -> Sandbox:
        return Sandbox(self)
