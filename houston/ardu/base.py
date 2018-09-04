from typing import List

from .sandbox import Sandbox
from ..system import System
from ..util import printflush
from ..action import ActionSchema
from ..state import Variable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    def __init__(self,
                 bug_name: str,
                 variables: List[Variable],
                 schemas: List[ActionSchema],
                 speedup: float = 3.0
                 ) -> None:
        assert speedup != 0.0
        self.__speedup = speedup

        variables += [
            Variable('homeLatitude',
                     lambda c: -35.362938),  # TODO: fixed
            Variable('homeLongitude',
                     lambda c: 149.165085),  # TODO: fixed
            Variable('altitude',
                     lambda c: c.connection.location.global_relative_frame.alt,  # noqa: pycodestyle
                     1.0),
            Variable('latitude',
                     lambda c: c.connection.location.global_relative_frame.lat,  # noqa: pycodestyle
                     0.0005),
            Variable('longitude',
                     lambda c: c.connection.location.global_relative_frame.lon,  # noqa: pycodestyle
                     0.0005),
            Variable('armable',
                     lambda c: c.connection.is_armable),
            Variable('armed', lambda c: c.connection.armed),
            Variable('mode', lambda c: c.connection.mode.name),
            Variable('vx', lambda c: c.connection.velocity[0], 0.05),
            Variable('vy', lambda c: c.connection.velocity[1], 0.05),
            Variable('vz', lambda c: c.connection.velocity[2], 0.05),
            Variable('pitch',
                     lambda c: c.connection.attitude.pitch, 0.05),
            Variable('yaw', lambda c: c.connection.attitude.yaw, 0.05),
            Variable('roll',
                     lambda c: c.connection.attitude.roll, 0.05),
            Variable('heading', lambda c: c.connection.heading, 2),
            Variable('airspeed',
                     lambda c: c.connection.airspeed, 0.05),
            Variable('groundspeed',
                     lambda c: c.connection.groundspeed, 0.05),
            Variable('ekf_ok', lambda c: c.connection.ekf_ok),
            Variable('throttle_channel',
                     lambda c: c.connection.channels['3']),
            Variable('roll_channel',
                             lambda c: c.connection.channels['1']),
        ]

        super(BaseSystem, self).__init__(bug_name, variables, schemas)

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
