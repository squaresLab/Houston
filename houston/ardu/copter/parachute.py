import time
import math

from houston.action import ActionSchema, Parameter, Action
from houston.branch import Branch, IdleBranch
from houston.valueRange import DiscreteValueRange


class ParachuteSchema(ActionSchema):
    """docstring for TakeoffActionSchema.
    
    Branches:
        Normally:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('parachute_action', DiscreteValueRange([0, 1, 2]))  # 0=disable, 1=enable, 2=release
        ]
        branches = [
            ParachuteNormally(self),
            IdleBranch(self)
        ]

        super(ParachuteSchema, self).__init__('parachute', parameters, branches)


    def dispatch(self, system, action, state, environment):
        from pymavlink import mavutil
        vehicle = system.vehicle
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_DO_PARACHUTE,
            0, action['parachute_action'], 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


class ParachuteNormally(Branch):
    def __init__(self, system):
        super(ParachuteNormally, self).__init__("normal", system)


    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset


    def postcondition(self, system, action, state_before, state_after, environment):
        return  not state_after['armed'] and \
                system.variable('altitude').lt(state_after['altitude'], 0.3)


    def precondition(self, system, action, state, environment):
        return  action['parachute_action'] == 2 and self.is_satisfiable(system, state, environment)


    def is_satisfiable(self, system, state, environment):
        return state['armed'] and \
                state['mode'] == 'GUIDED' and \
                system.variable('altitude').gt(state['altitude'], 0.3)


    def generate(self, system, state, env, rng):
        return self.schema.generate(rng)
