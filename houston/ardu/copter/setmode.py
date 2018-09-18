__all__ = ['SetModeSchema', 'SetModeLand', 'SetModeGuided', 'SetModeLoiter',
           'SetModeRTL']

import time
import logging

import dronekit
import geopy

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...command import CommandSchema, Parameter, Command
from ...specification import Specification, Idle
from ...valueRange import DiscreteValueRange

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class SetModeSchema(CommandSchema):
    """
    Branches:
        Guided:
        Loiter:
        RTL:
        Land:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('mode',
                      DiscreteValueRange(['GUIDED', 'LOITER', 'RTL', 'LAND']))
        ]
        specs = [
            SetModeGuided(),
            SetModeLoiter(),
            SetModeRTL(),
            SetModeLand(),
            Idle()
        ]
        super().__init__('setmode', parameters, specs)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 cmd: Command,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        sandbox.connection.mode = dronekit.VehicleMode(cmd['mode'])


class SetModeLand(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c: a['mode'] == 'LAND' and s.altitude > 0.3

        def post(a, s0, s1, e, c) -> bool:
            delta_lon = 0.1
            delta_lat = 0.1
            delta_alt = 1.0
            sat_mode = s1.mode == 'LAND'
            sat_lon = abs(s1.longitude - s0.longitude) < delta_lon
            sat_lat = abs(s1.latitude - s0.latitude) < delta_lat
            sat_alt = abs(s1.altitude - 0.3) < delta_alt
            return sat_lon and sat_lat and sat_alt

        def timeout(a, s, e, c) -> float:
            timeout = s.altitude * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__('land', pre, post, timeout)


class SetModeGuided(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c: a['mode'] == 'GUIDED'
        post = lambda a, s0, s1, e, c: s1.mode == 'GUIDED'
        timeout = lambda a, s, e, c: c.constant_timeout_offset
        super().__init__('guided', pre, post, timeout)


class SetModeLoiter(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c: a['mode'] == 'LOITER'
        post = lambda a, s0, s1, e, c: s1.mode == 'LOITER'
        timeout = lambda a, s, e, c: c.constant_timeout_offset
        super().__init__('loiter', pre, post, timeout)


class SetModeRTL(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c: a['mode'] == 'RTL'

        def post(a, s0, s1, e, c) -> bool:
            if s1.mode != 'RTL':
                return False  # hmmm?

            if s1.altitude < 0.3:
                if s0.armed != s1.armed:
                    return False
            elif s0.armed:
                return False

            err_alt = 1.0
            err_lat = 0.1
            err_lon = 0.1

            sat_alt = abs(s1.altitude) <= noise_alt
            diff_lat = abs(s1.latitude - s0.home_latitude)
            sat_lat = diff_lat <= noise_lat
            diff_lon = abs(s1.longitude - s0.home_longitude)
            sat_lon = diff_lon <= err_lon

            return sat_alt and sat_lat and sat_lon

        def timeout(a, s, e, c) -> float:
            from_loc = (s.latitude, s.longitude)
            to_loc = (s.home_latitude, s.home_longitude)
            dist = geopy.distance.great_circle(from_loc, to_loc).meters

            time_goto_phase = dist * c.time_per_metre_travelled
            time_land_phase = state.altitude * c.time_per_metre_travelled

            timeout = \
                time_goto_phase + time_land_phase + c.constant_timeout_offset
            return timeout

        super().__init__('rtl', pre, post, timeout)
