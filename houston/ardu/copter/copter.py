__all__ = ['ArduCopter']

import logging

from bugzoo.client import Client as BugZooClient
from bugzoo.core.bug import Bug as Snapshot

from .state import State
from .sandbox import Sandbox
from ..base import BaseSystem
from ..configuration import Configuration

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class ArduCopter(BaseSystem):
    state = State
    schemas = []

    def __init__(self,
                 snapshot: Snapshot,
                 configuration: Configuration
                 ) -> None:
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.copter.goto import GoToSchema
        from houston.ardu.copter.setmode import SetModeSchema
        from houston.ardu.copter.takeoff import TakeoffSchema
        from houston.ardu.copter.parachute import ParachuteSchema
        schemas = [
            GoToSchema(),
            TakeoffSchema(),
            ArmDisarmSchema(),
            SetModeSchema(),
            ParachuteSchema()
        ]
        super().__init__(snapshot, schemas, configuration)

    def provision(self, client_bugzoo: BugZooClient) -> Sandbox:
        return Sandbox(self, client_bugzoo)
