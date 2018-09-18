__all__ = ['GotoNormally', 'GotoLoiter']

from typing import Tuple

import geopy
import geopy.distance

from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...valueRange import ContinuousValueRange, DiscreteValueRange
from ...specification import Specification, Idle


class GotoNormally(Specification):
    """
    If the robot is armed and not in its `LOITER` mode, GoTo actions should
    cause the robot to move to the desired location. For certain Ardu systems,
    the precondition on this normal behaviour is stronger; for more
    information, refer to the system-specific subclasses of GotoNormally.
    """
    def __init__(self) -> None:
        super().__init__('normal')

    def timeout(self, action, state, environment, config):
        from_loc = (state.latitude, state.longitude)
        to_loc = (action['latitude'], action['longitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters
        timeout = dist * config.time_per_metre_travelled
        timeout += config.constant_timeout_offset
        return timeout

    def precondition(self, action, state, environment, config):
        """
        This behaviour will occur for Goto actions when the system is armed and
        not in its `LOITER` mode.
        """
        return state.armed and state.mode != 'LOITER'

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        """
        Upon completion of the action, the robot should be at the longitude and
        latitude specified by the action parameters.
        """
        err_lon = 0.1
        err_lat = 0.1
        sat_lon = \
            abs(state_after.longitude - action['longitude']) <= err_lon
        sat_lat = \
            abs(state_after.latitude - action['latitude']) <= err_lat
        return sat_lon and sat_lat

    def is_satisfiable(self, state, environment, config):
        return self.precondition(None, state, environment, config)

    def generate(self, state, environment, config, rng):
        return self.schema.generate(rng)


class GotoLoiter(Specification):
    """
    If the robot is armed and in its `LOITER` mode, GoTo actions should have no
    effect upon the robot. (Why isn't this covered by Idle?)
    """
    def __init__(self) -> None:
        super().__init__('loiter')

    def timeout(self, action, state, environment, config):
        return config.constant_timeout_offset

    def precondition(self, action, state, environment, config):
        return state.armed and state.mode == 'LOITER'

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config):
        sat_mode = state_after.mode == 'LOITER'
        # FIXME 82
        err_lon = 0.1
        err_lat = 0.1
        err_alt = 0.5
        sat_lon = \
            abs(state_after.longitude - state_before.longitude) <= err_lon
        sat_lat = \
            abs(state_after.latitude - state_before.latitude) <= err_lat
        sat_alt = \
            abs(state_after.altitude - state_before.altitude) <= err_alt
        return sat_mode and sat_lon and sat_lat and sat_alt

    def is_satisfiable(self, state, environment, config):
        return self.precondition(None, state, environment, config)

    def generate(self, state, environment, config, rng):
        return self.schema.generate(rng)
