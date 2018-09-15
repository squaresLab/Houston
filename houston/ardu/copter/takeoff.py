__all__ = ['TakeoffSchema', 'TakeoffNormally']

import time
import math

from pymavlink import mavutil

from ...configuration import Configuration
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
        super().__init__('takeoff', parameters, branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        vehicle = sandbox.connection
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF,
            0, 1, 0, 0, 0, 0, 0, action['altitude'])
        vehicle.send_mavlink(msg)


class TakeoffNormally(Branch):
    def __init__(self, schema):
        super().__init__("normal", schema)

    def timeout(self, action, state, environment, config):
        # FIXME add rate of ascent
        delta_alt = abs(action['altitude'] - state.altitude)
        timeout = delta_alt * config.time_per_metre_travelled
        timeout += config.constant_timeout_offset
        return timeout

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config
                      ) -> bool:
        # FIXME #82
        err_lon = 0.1
        err_lat = 0.1
        err_alt = 0.1
        err_vz = 0.1
        sat_lon = \
            abs(state_before.longitude - state_after.longitude) <= err_lon
        sat_lat = \
            abs(state_before.latitude - state_after.latitude) <= err_lat
        sat_alt = abs(state_after.altitude - action['altitude']) <= err_alt
        sat_vz = abs(state_after.vz) < err_vz
        return sat_lon and sat_lat and sat_alt and sat_vz

    def precondition(self, action, state, environment, config):
        # FIXME #82
        err_alt = 0.5
        sat_armed = state.armed
        sat_mode = state.mode == 'GUIDED'
        sat_alt = state.altitude - err_alt <= 0.3
        return sat_armed and sat_mode and sat_alt

    def is_satisfiable(self, state, environment, config):
        return self.precondition(None, state, environment, config)

    def generate(self, state, env, config, rng):
        return self.schema.generate(rng)
