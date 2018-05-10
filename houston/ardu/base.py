from houston.system import System
from houston.util import printflush
from houston.action import ActionSchema
from .sandbox import Sandbox
from ..state import StateVariable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    def __init__(self,
                 bug_name: str,
                 variables: 'List[StateVariable]',
                 schemas: 'List[ActionSchema]',
                 speedup: float = 3.0
                 ) -> None:
        assert speedup != 0.0
        self.__speedup = speedup

        variables += [
            StateVariable('homeLatitude', lambda c: -35.362938), # TODO: fixed
            StateVariable('homeLongitude', lambda c: 149.165085), # TODO: fixed
            StateVariable('altitude', lambda c: c.connection.location.global_relative_frame.alt, 1.0),
            StateVariable('latitude', lambda c: c.connection.location.global_relative_frame.lat, 0.0005),
            StateVariable('longitude', lambda c: c.connection.location.global_relative_frame.lon, 0.0005),
            StateVariable('armable', lambda c: c.connection.is_armable),
            StateVariable('armed', lambda c: c.connection.armed),
            StateVariable('mode', lambda c: c.connection.mode.name),
            StateVariable('vx', lambda c: c.connection.velocity[0], 0.05),
            StateVariable('vy', lambda c: c.connection.velocity[1], 0.05),
            StateVariable('vz', lambda c: c.connection.velocity[2], 0.05),
            StateVariable('pitch', lambda c: c.connection.attitude.pitch, 0.05),
            StateVariable('yaw', lambda c: c.connection.attitude.yaw, 0.05),
            StateVariable('roll', lambda c: c.connection.attitude.roll, 0.05),
            StateVariable('heading', lambda c: c.connection.heading, 2),
            StateVariable('airspeed', lambda c: c.connection.airspeed, 0.05),
            StateVariable('groundspeed', lambda c: c.connection.groundspeed, 0.05),
            StateVariable('ekf_ok', lambda c: c.connection.ekf_ok),
            StateVariable('throttle_channel', lambda c: c.connection.channels['3']),
            StateVariable('roll_channel', lambda c: c.connection.channels['1']),
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
