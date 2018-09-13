__all__ = ['ArduRover']

import time

from bugzoo.client import Client as BugZooClient
from bugzoo.core.bug import Bug as Snapshot

from .sandbox import Sandbox
from ...util import printflush
from ..base import BaseSystem
from .state import State


class ArduRover(BaseSystem):

    state = State

    def __init__(self,
                 snapshot: Snapshot,
                 speedup=3.0
                 ) -> None:
        from ..common import ArmDisarmSchema
        from .goto import GoToSchema

        # TODO: RTL_ALT: http://ardupilot.org/copter/docs/rtl-mode.html
        # rover-specific system variables
        schemas = [
            GoToSchema(),
            ArmDisarmSchema()
        ]

        super(ArduRover, self).__init__(snapshot,
                                        schemas,
                                        speedup=speedup)

    def provision(self, client_bugzoo: BugZooClient) -> Sandbox:
        return Sandbox(self, client_bugzoo)
