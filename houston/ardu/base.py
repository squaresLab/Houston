import bugzoo
from houston.system import System
from houston.util import printflush
from houston.action import ActionSchema
from houston.ardu.sandbox import Sandbox
from houston.state import   StateVariable, \
                            InternalVariable, \
                            ExternalVariable


class BaseSystem(System):
    """
    Description of the ArduCopter system
    """
    def __init__(self,
                 snapshot: bugzoo.Bug,
                 variables: 'List[StateVariable]',
                 schemas: 'List[ActionSchema]',
                 speedup: float = 3.0
                 ) -> None:
        assert speedup != 0.0
        self.__speedup = speedup

        variables += [
            InternalVariable('homeLatitude', lambda c: -35.362938), # TODO: fixed
            InternalVariable('homeLongitude', lambda c: 149.165085), # TODO: fixed
            InternalVariable('altitude', lambda c: c.connection.location.global_relative_frame.alt, 1.0),
            InternalVariable('latitude', lambda c: c.connection.location.global_relative_frame.lat, 0.0005),
            InternalVariable('longitude', lambda c: c.connection.location.global_relative_frame.lon, 0.0005),
            InternalVariable('armable', lambda c: c.connection.is_armable),
            InternalVariable('armed', lambda c: c.connection.armed),
            InternalVariable('mode', lambda c: c.connection.mode.name),
            InternalVariable('vx', lambda c: c.connection.velocity[0], 0.05),
            InternalVariable('vy', lambda c: c.connection.velocity[1], 0.05),
            InternalVariable('vz', lambda c: c.connection.velocity[2], 0.05),
            InternalVariable('pitch', lambda c: c.connection.attitude.pitch, 0.05),
            InternalVariable('yaw', lambda c: c.connection.attitude.yaw, 0.05),
            InternalVariable('roll', lambda c: c.connection.attitude.roll, 0.05),
            InternalVariable('heading', lambda c: c.connection.heading, 2),
            InternalVariable('airspeed', lambda c: c.connection.airspeed, 0.05),
            InternalVariable('groundspeed', lambda c: c.connection.groundspeed, 0.05),
            InternalVariable('ekf_ok', lambda c: c.connection.ekf_ok),
            InternalVariable('throttle_channel', lambda c: c.connection.channels['3']),
            InternalVariable('roll_channel', lambda c: c.connection.channels['1']),
        ]

        super(BaseSystem, self).__init__(snapshot, variables, schemas)

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
