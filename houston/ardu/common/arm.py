__all__ = ['ArmDisarmSchema']

import time

from pymavlink import mavutil

from ...configuration import Configuration
from ...action import ActionSchema, Parameter, Action
from ...specification import Specification, Idle
from ...state import State
from ...environment import Environment
from ...valueRange import DiscreteValueRange
from ..sandbox import Sandbox


class ArmDisarmSchema(ActionSchema):
    """
    Behaviours:
        Normal: if the robot is armable and is in either its 'GUIDED' or
            'LOITER' modes, the robot will become armed.
        Idle: if the conditions above cannot be met, the robot will ignore the
            command.
    """
    def __init__(self) -> None:
        name = 'arm'
        parameters = [
            Parameter('arm', DiscreteValueRange([True, False]))
        ]
        specs = [
            ArmNormally(),
            DisarmNormally(),
            Idle()
        ]
        super().__init__(name, parameters, specs)

    def dispatch(self,
                 sandbox: Sandbox,
                 action: Action,
                 state: State,
                 environment: Environment,
                 configuration: Configuration
                 ) -> None:
        vehicle = sandbox.connection
        arm_flag = 1 if action['arm'] else 0
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM,
            0, arm_flag, 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


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
