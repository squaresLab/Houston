import time

from houston.ardu.base import CONSTANT_TIMEOUT_OFFSET
from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.valueRange import DiscreteValueRange


class ArmSchema(ActionSchema):
    """
    TODO: docstring
    
    Behaviours:
   
        Normal: if the robot is armable and is in either its 'GUIDED' or
            'LOITER' modes, the robot will become armed.
        Idle: if the conditions above cannot be met, the robot will ignore the
            command.
    """
    def __init__(self):
        parameters = []
        branches = [
            ArmNormally(self),
            IdleBranch(self)
        ]
        super(ArmSchema, self).__init__('arm', parameters, branches)


    def dispatch(self, system, action, state, environment):
        from pymavlink import mavutil
        vehicle = system.vehicle
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM,
            0, 1, 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


class ArmNormally(Branch):
    def __init__(self, system):
        super(ArmNormally, self).__init__('normal', system)


    def precondition(self, system, action, state, environment):
        return  state['armable'] and \
                state['mode'] in ['GUIDED', 'LOITER']


    def postcondition(self, system, action, state_before, state_action, environment):
        return state['armed']


    def timeout(self, system, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def is_satisfiable(self, system, state, environment):
        return self.precondition(system, None, state, environment)


    def generate(self, state, environment, rng):
        return self.schema.generate(rng)
