__all__ = ['GotoLoiter', 'ArmDisarm']

import time

import geopy
import geopy.distance
from pymavlink import mavutil

from .sandbox import Sandbox
from ..state import State
from ..environment import Environment
from ..valueRange import ContinuousValueRange, DiscreteValueRange
from ..configuration import Configuration
from ..command import Parameter, Command
from ..specification import Specification, Idle


class ArmNormally(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c:\
            a['arm'] and s.armable and s.mode in ['GUIDED', 'LOITER']
        post = lambda a, s0, s1, e, c: s1.armed
        timeout = lambda a, s, e, c: c.constant_timeout_offset + 1.0
        super().__init__('arm-normal', pre, post, timeout)


class DisarmNormally(Specification):
    def __init__(self) -> None:
        pre = lambda a, s, e, c:\
            a['arm'] and s.armed
        post = lambda a, s0, s1, e, c: not s1.armed
        timeout = lambda a, s, e, c: c.constant_timeout_offset + 1.0
        super().__init__('disarm-normal', pre, post, timeout)


class GotoLoiter(Specification):
    """
    If the robot is armed and in its `LOITER` mode, GoTo actions should have no
    effect upon the robot. (Why isn't this covered by Idle?)
    """
    def __init__(self) -> None:
        pre = lambda a, s, e, c: s.armed and s.mode == 'LOITER'
        timeout = lambda a, s, e, c: c.constant_timeout_offset

        def post(a, s0, s1, e, c) -> bool:
            sat_mode = s1.mode == 'LOITER'
            # FIXME 82
            err_lon = 0.1
            err_lat = 0.1
            err_alt = 0.5
            sat_lon = abs(s1.longitude - s0.longitude) <= err_lon
            sat_lat = abs(s1.latitude - s0.latitude) <= err_lat
            sat_alt = abs(s1.altitude - s0.altitude) <= err_alt
            return sat_mode and sat_lon and sat_lat and sat_alt

        super().__init__('loiter', pre, post, timeout)


class ArmDisarm(Command):
    """
    Behaviours:
        Normal: if the robot is armable and is in either its 'GUIDED' or
            'LOITER' modes, the robot will become armed.
        Idle: if the conditions above cannot be met, the robot will ignore the
            command.
    """
    name = 'arm'
    parameters = [
        Parameter('arm', DiscreteValueRange([True, False]))
    ]
    specifications = [
        ArmNormally(),
        DisarmNormally(),
        Idle()
    ]

    def dispatch(self,
                 sandbox: Sandbox,
                 state: State,
                 environment: Environment,
                 configuration: Configuration
                 ) -> None:
        vehicle = sandbox.connection
        arm_flag = 1 if self.arm else 0
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM,
            0, arm_flag, 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)
