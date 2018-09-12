__all__ = ['TakeoffSchema', 'TakeoffNormally']

import time
import math

from pymavlink import mavutil

from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...branch import Branch, IdleBranch
from ...valueRange import ContinuousValueRange


class TakeoffSchema(ActionSchema):
    """
    Branches:
        Normally:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]
        branches = [
            TakeoffNormally(self),
            IdleBranch(self)
        ]

        super(TakeoffSchema, self).__init__('takeoff', parameters, branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment
                 ) -> None:
        vehicle = sandbox.connection
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF,
            0, 1, 0, 0, 0, 0, 0, action['altitude'])
        vehicle.send_mavlink(msg)


class TakeoffNormally(Branch):
    def __init__(self, system):
        super(TakeoffNormally, self).__init__("normal", system)

    def timeout(self, system, action, state, environment):
        timeout = action['altitude'] * system.time_per_metre_travelled
        timeout += system.constant_timeout_offset
        return timeout

    def postcondition(self,
                      system,
                      action,
                      state_before,
                      state_after,
                      environment
                      ) -> bool:
        v = system.variable
        sat_lon = v('longitude').eq(state_before['longitude'],
                                    state_after['longitude'])
        sat_lat = v('latitude').eq(state_before['latitude'],
                                   state_after['latitude'])
        sat_alt = v('altitude').eq(state_after['altitude'],
                                   action['altitude'])
        sat_vz = v('vz').eq(state_after['vz'], 0.0)
        return sat_lon and sat_lat and sat_alt and sat_vz

    def precondition(self, system, action, state, environment):
        return state['armed'] and \
            state['mode'] == 'GUIDED' and \
            system.variable('altitude').lt(state['altitude'], 0.3)

    def is_satisfiable(self, system, state, environment):
        return self.precondition(system, None, state, environment)

    def generate(self, system, state, env, rng):
        return self.schema.generate(rng)
