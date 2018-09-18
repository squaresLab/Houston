__all__ = ['TakeoffSchema', 'TakeoffNormally']

import time
import math

from pymavlink import mavutil

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...command import CommandSchema, Parameter, Command
from ...specification import Specification, Idle
from ...valueRange import ContinuousValueRange


class TakeoffSchema(CommandSchema):
    """
    Branches:
        Normally:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]
        specs = [
            TakeoffNormally(),
            Idle()
        ]
        super().__init__('takeoff', parameters, specs)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 cmd: Command,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        vehicle = sandbox.connection
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF,
            0, 1, 0, 0, 0, 0, 0, cmd['altitude'])
        vehicle.send_mavlink(msg)


class TakeoffNormally(Specification):
    def __init__(self) -> None:
        def pre(a, s, e, c) -> bool:
            # FIXME #82
            err_alt = 0.5
            sat_armed = s.armed
            sat_mode = s.mode == 'GUIDED'
            sat_alt = s.altitude - err_alt <= 0.3
            return sat_armed and sat_mode and sat_alt

        def post(a, s0, s1, e, c) -> bool:
            # FIXME #82
            err_lon = 0.1
            err_lat = 0.1
            err_alt = 0.1
            err_vz = 0.1
            sat_lon = abs(s0.longitude - s1.longitude) <= err_lon
            sat_lat = abs(s0.latitude - s1.latitude) <= err_lat
            sat_alt = abs(s1.altitude - a['altitude']) <= err_alt
            sat_vz = abs(s1.vz) < err_vz
            return sat_lon and sat_lat and sat_alt and sat_vz

        def timeout(a, s, e, c) -> float:
            # FIXME add rate of ascent
            delta_alt = abs(a['altitude'] - s.altitude)
            t = delta_alt * c.time_per_metre_travelled
            t += c.constant_timeout_offset
            return t

        super().__init__("normal", pre, post, timeout)
