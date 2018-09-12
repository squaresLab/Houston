__all__ = ['ArduCopter']

from bugzoo.core.bug import Bug as Snapshot

from .state import State
from .sandbox import Sandbox
from ..base import BaseSystem


class ArduCopter(BaseSystem):
    state = State

    def __init__(self,
                 snapshot: Snapshot,
                 speedup: float = 3.0,
                 min_parachute_alt: float = 10.0
                 ) -> None:
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.copter.goto import GoToSchema
        from houston.ardu.copter.setmode import SetModeSchema
        from houston.ardu.copter.takeoff import TakeoffSchema
        from houston.ardu.copter.parachute import ParachuteSchema

        assert speedup != 0.0
        self.__min_parachute_alt = min_parachute_alt

        schemas = [
            GoToSchema(),
            TakeoffSchema(),
            ArmDisarmSchema(),
            SetModeSchema(),
            ParachuteSchema()
        ]
        super(ArduCopter, self).__init__(snapshot,
                                         schemas,
                                         speedup=speedup)

    @property
    def min_parachute_alt(self) -> float:
        return self.__min_parachute_alt

    def provision(self) -> Sandbox:
        return Sandbox(self)
