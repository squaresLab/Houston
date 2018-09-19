__all__ = ['GoTo']

import dronekit
import geopy.distance

from ..common import GotoLoiter
from ...specification import Specification
from ...configuration import Configuration
from ...command import Command, Parameter
from ...state import State
from ...environment import Environment
from ...specification import Idle
from ...valueRange import ContinuousValueRange, DiscreteValueRange


class GotoNormally(Specification):
    """
    If the robot is armed and not in its `LOITER` mode, GoTo actions should
    cause the robot to move to the desired location. For certain Ardu systems,
    the precondition on this normal behaviour is stronger; for more
    information, refer to the system-specific subclasses of GotoNormally.
    """
    def __init__(self) -> None:
        def pre(a, s, e, c) -> bool:
            # FIXME 82
            sat_armed = s.armed
            sat_mode = s.mode != 'LOITER'
            err_alt = 0.1
            sat_alt = s.altitude + err_alt > 0.3
            return sat_armed and sat_mode and sat_alt

        def post(a, s0, s1, e, c) -> bool:
            # FIXME 82
            err_lon = 0.1
            err_lat = 0.1
            err_alt = 0.1
            sat_lon = abs(s1.longitude - a['longitude']) <= err_lon
            sat_lat = abs(s1.latitude - a['latitude']) <= err_lat
            sat_alt = abs(s1.altitude - a['altitude']) <= err_alt
            return sat_lon and sat_lat and sat_alt

        def timeout(a, s, e, c) -> float:
            from_loc = (s.latitude, s.longitude)
            to_loc = (a['latitude'], a['longitude'])
            dist = geopy.distance.great_circle(from_loc, to_loc).meters
            timeout = dist * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__('normal', pre, post, timeout)


class GoTo(Command):
    name = 'goto'
    parameters = [
        Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
        Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
        Parameter('altitude', ContinuousValueRange(0.3, 100.0))
    ]
    specifications = [
        GotoNormally(),
        GotoLoiter(),
        Idle()
    ]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        loc = dronekit.LocationGlobalRelative(self.latitude,
                                              self.longitude,
                                              self.altitude)
        sandbox.connection.simple_goto(loc)
