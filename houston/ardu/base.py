__all__ = ['BaseSystem']

from typing import List

from bugzoo.core.bug import Bug as Snapshot

from .sandbox import Sandbox
from ..system import System
from ..util import printflush
from ..action import ActionSchema
from ..state import Variable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    is_abstract = True

    def __init__(self,
                 snapshot: Snapshot,
                 schemas: List[ActionSchema],
                 speedup: float = 3.0
                 ) -> None:
        assert speedup != 0.0
        self.__speedup = speedup
        super().__init__(schemas, snapshot)

    def provision(self) -> Sandbox:
        return Sandbox(self)

    @property
    def speedup(self) -> float:
        return self.__speedup

    # TODO: internally, this should be a function of speedup
    @property
    def time_per_metre_travelled(self) -> float:
        return 1.0

    @property
    def constant_timeout_offset(self) -> float:
        """
        The constant offset that is added to all timeouts (the pinch of salt)
        """
        return 1.0
