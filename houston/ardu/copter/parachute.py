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
        def pre(a, s, e, c) -> bool:
            # FIXME #82
            sat_action = a['parachute_action'] == 2
            noise_alt = 0.1
            sat_armed = s.armed
            sat_mode = s.mode == 'GUIDED'
            sat_alt = s.alt > c.min_parachute_alt - noise_alt
            return sat_action and sat_armed and sat_mode and sat_alt

        def post(a, s0, s1, e, c) -> bool:
            # FIXME #82
            noise_alt = 0.1
            noise_vz = 0.05
            sat_armed = not s1.armed
            sat_alt = s1.altitude < 0.3 + noise_alt
            sat_vz = 0.0 <= s1.vz <= noise_vz
            return sat_armed and sat_alt and sat_vz

        def timeout(a, s, e, c) -> float:
            timeout = s.altitude * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__("normal", pre, post, timeout)
