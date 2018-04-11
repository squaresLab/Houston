from houston.ardu.base import BaseSystem
from houston.ardu.copter.sandbox import Sandbox


class ArduCopter(BaseSystem):
    def __init__(self,
                 bug_name: str,
                 speedup: float = 3.0,
                 min_parachute_alt: float = 10.0):
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.copter.goto import GoToSchema
        from houston.ardu.copter.setmode import SetModeSchema
        from houston.ardu.copter.takeoff import TakeoffSchema
        from houston.ardu.copter.parachute import ParachuteSchema

        assert speedup != 0.0
        self.__min_parachute_alt = min_parachute_alt

        # variables specific to the ArduCopter system
        variables = []
        schemas = [
            GoToSchema(),
            TakeoffSchema(),
            ArmDisarmSchema(),
            SetModeSchema(),
            ParachuteSchema()
        ]
        super(ArduCopter, self).__init__(bug_name,
                                         variables,
                                         schemas,
                                         speedup=speedup)

    @property
    def min_parachute_alt(self) -> float:
        return self.__min_parachute_alt


    def provision(self) -> Sandbox:
        return Sandbox(self)

