__all__ = ['ArduRover']

from bugzoo.client import Client as BugZooClient
from bugzoo.core.bug import Bug as Snapshot

from .sandbox import Sandbox
from .state import State
from ..base import BaseSystem
from ..configuration import Configuration


class ArduRover(BaseSystem):
    state = State

    def __init__(self,
                 snapshot: Snapshot,
                 config: Configuration
                 ) -> None:
        from ..common import ArmDisarmSchema
        from .goto import GoToSchema

        # TODO: RTL_ALT: http://ardupilot.org/copter/docs/rtl-mode.html
        # rover-specific system variables
        schemas = [
            GoToSchema(),
            ArmDisarmSchema()
        ]
        super().__init__(snapshot, schemas, config)

    def provision(self, client_bugzoo: BugZooClient) -> Sandbox:
        return Sandbox(self, client_bugzoo)
