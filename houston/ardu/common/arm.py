import time

from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.valueRange import DiscreteValueRange


class ArmDisarmSchema(ActionSchema):
    """
    TODO: docstring
    
    Behaviours:
   
        Normal: if the robot is armable and is in either its 'GUIDED' or
            'LOITER' modes, the robot will become armed.
        Idle: if the conditions above cannot be met, the robot will ignore the
            command.
    """
    def __init__(self):
        parameters = [
            Parameter('arm', DiscreteValueRange([True, False]))
        ]
        branches = [
            ArmNormally(self),
            DisarmNormally(self),
            IdleBranch(self)
        ]
        super(ArmDisarmSchema, self).__init__('arm', parameters, branches)


    def dispatch(self, system, action, state, environment):
        from pymavlink import mavutil
        vehicle = system.vehicle
        arm_flag = 1 if action['arm'] else 0
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM,
            0, arm_flag, 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


class ArmNormally(Branch):
    def __init__(self, system):
        super(ArmNormally, self).__init__('arm-normal', system)


    def precondition(self, system, action, state, environment):
        return  action['arm'] and self.is_satisfiable(system, state, environment)


    def postcondition(self, system, action, state_before, state_after, environment):
        return state_after['armed']


    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset


    def is_satisfiable(self, system, state, environment):
        return state['armable'] and state['mode'] in ['GUIDED', 'LOITER']


    def generate(self, system, state, environment, rng):
        return {'arm': True}


class DisarmNormally(Branch):
    def __init__(self, system):
        super(DisarmNormally, self).__init__('disarm-normal', system)


    def precondition(self, system, action, state, environment):
        return  not action['arm'] and self.is_satisifiable(system, state, environment)


    def postcondition(self, system, action, state_before, state_after, environment):
        return not state_after['armed']


    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset


    # TODO
    def is_satisfiable(self, system, state, environment):
        return state['armed']# and state['mode'] in ['GUIDED', 'LOITER']


    def generate(self, system, state, environment, rng):
        return {'arm': False}
