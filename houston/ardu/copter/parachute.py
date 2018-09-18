__all__ = ['ParachuteSchema', 'ParachuteNormally']

from pymavlink import mavutil

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...specification import Specification, Idle
from ...valueRange import DiscreteValueRange


class ParachuteSchema(ActionSchema):
    def __init__(self):
        name = 'parachute'
        parameters = [
            # 0=disable, 1=enable, 2=release
            Parameter('parachute_action', DiscreteValueRange([0, 1, 2]))
        ]
        specs = [
            ParachuteNormally(),
            Idle()
        ]
        super().__init__(name, parameters, specs)

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
            mavutil.mavlink.MAV_CMD_DO_PARACHUTE,
            0, action['parachute_action'], 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


class ParachuteNormally(Specification):
    def __init__(self):
        super().__init__("normal")

    def timeout(self, action, state, environment, config):
        timeout = state.altitude * config.time_per_metre_travelled
        timeout += config.constant_timeout_offset
        return timeout

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        # FIXME #82
        noise_alt = 0.1
        noise_vz = 0.05
        sat_armed = not state_after.armed
        sat_alt = state_after.altitude < 0.3 + noise_alt
        sat_vz = 0.0 <= state_after.vz <= noise_vz
        return sat_armed and sat_alt and sat_vz

    def precondition(self, action, state, environment, config):
        return action['parachute_action'] == 2 and \
            self.is_satisfiable(state, environment, config)

    def is_satisfiable(self, state, environment, config):
        # FIXME #82
        noise_alt = 0.1
        sat_armed = state.armed
        sat_mode = state.mode == 'GUIDED'
        sat_alt = state.alt > config.min_parachute_alt - noise_alt
        return sat_armed and sat_mode and sat_alt
