__all__ = ['SetModeSchema', 'SetModeLand', 'SetModeGuided', 'SetModeLoiter',
           'SetModeRTL']

import time
import logging

import dronekit
import geopy

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...specification import Specification, Idle
from ...valueRange import DiscreteValueRange

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class SetModeSchema(ActionSchema):
    """
    Branches:
        Guided:
        Loiter:
        RTL:
        Land:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('mode',
                      DiscreteValueRange(['GUIDED', 'LOITER', 'RTL', 'LAND']))
        ]
        specs = [
            SetModeGuided(),
            SetModeLoiter(),
            SetModeRTL(),
            SetModeLand(),
            Idle()
        ]
        super().__init__('setmode', parameters, specs)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        sandbox.connection.mode = dronekit.VehicleMode(action['mode'])


class SetModeLand(Specification):
    def __init__(self) -> None:
        super().__init__('land')

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
        delta_lon = 0.1
        delta_lat = 0.1
        delta_alt = 1.0
        sat_mode = state_after.mode == 'LAND'
        sat_lon = \
            abs(state_after.longitude - state_before.longitude) < delta_lon
        sat_lat = \
            abs(state_after.latitude - state_before.latitude) < delta_lat
        sat_alt = \
            abs(state_after.altitude - 0.3) < delta_alt
        return sat_lon and sat_lat and sat_alt

    def precondition(self, action, state, environment, config):
        return action['mode'] == 'LAND' and state.altitude > 0.3

    def is_satisfiable(self, state, environment, config):
        return state.altitude > 0.3

    def generate(self, state, environment, config, rng):
        return Action(self.schema.name, {'mode': 'LAND'})


class SetModeGuided(Specification):
    def __init__(self) -> None:
        super().__init__('guided')

    def timeout(self, action, state, environment, config):
        return config.constant_timeout_offset

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        return state_after.mode == 'GUIDED'

    def precondition(self, action, state, environment, config):
        return action['mode'] == 'GUIDED'

    def is_satisfiable(self, state, environment, config):
        return True

    def generate(self, state, environment, config, rng):
        return Action(self.schema.name, {'mode': 'GUIDED'})


class SetModeLoiter(Specification):
    def __init__(self) -> None:
        super().__init__('loiter')

    def timeout(self, action, state, environment, config):
        return config.constant_timeout_offset

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        return state_after.mode == 'LOITER'

    def precondition(self, action, state, environment, config):
        return action['mode'] == 'LOITER'

    def is_satisfiable(self, state, environment, config):
        return True

    def generate(self, state, environment, config, rng):
        return Action(self.schema.name, {'mode': 'LOITER'})


class SetModeRTL(Specification):
    def __init__(self) -> None:
        super().__init__('rtl')

    def timeout(self, action, state, environment, config):
        # compute distance
        from_loc = (state.latitude, state.longitude)
        to_loc = (state.home_latitude, state.home_longitude)
        dist = geopy.distance.great_circle(from_loc, to_loc).meters

        # compute time taken to travel from A to B, and time taken to land
        time_goto_phase = dist * config.time_per_metre_travelled
        time_land_phase = state.altitude * config.time_per_metre_travelled

        # TODO: what was this? No explanation of logic?
        # Land times and adjustment time for altitude
        # total_go_up_down_time = \
        #    math.fabs(10 - state['altitude']) *
        # config.time_per_metre_travelled

        # compute total timeout
        timeout = \
            time_goto_phase + time_land_phase + config.constant_timeout_offset

        logger.debug("calculated timeout: %.3f seconds", timeout)
        return timeout

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        if state_after.mode != 'RTL':
            return False  # hmmm?

        if state_before.altitude < 0.3:
            if state_before.armed != state_after.armed:
                return False
        elif state_before.armed:
            return False

        err_alt = 1.0
        err_lat = 0.1
        err_lon = 0.1

        sat_alt = abs(state_after.altitude) <= noise_alt
        diff_lat = abs(state_after.latitude - state_before.home_latitude)
        sat_lat = diff_lat <= noise_lat
        diff_lon = abs(state_after.longitude - state_before.home_longitude)
        sat_lon = diff_lon <= err_lon

        return sat_alt and sat_lat and sat_lon

    def precondition(self, action, state, environment, config):
        return action['mode'] == 'RTL'

    def is_satisfiable(self, state, environment, config):
        return True

    def generate(self, state, environment, config, rng):
        return Action(self.schema.name, {'mode': 'RTL'})
