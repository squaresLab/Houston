__all__ = ['GotoNormally', 'GotoLoiter', 'CircleBasedGotoGenerator']

from typing import Tuple

import geopy
import geopy.distance

from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action, ActionGenerator
from ...valueRange import ContinuousValueRange, DiscreteValueRange
from ...branch import Branch, IdleBranch


class GotoNormally(Branch):
    """
    If the robot is armed and not in its `LOITER` mode, GoTo actions should
    cause the robot to move to the desired location. For certain Ardu systems,
    the precondition on this normal behaviour is stronger; for more
    information, refer to the system-specific subclasses of GotoNormally.
    """
    def __init__(self, schema) -> None:
        super().__init__('normal', schema)

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
        return state['armed'] and state['mode'] != 'LOITER'

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


class GotoLoiter(Branch):
    """
    If the robot is armed and in its `LOITER` mode, GoTo actions should have no
    effect upon the robot. (Why isn't this covered by Idle?)
    """
    def __init__(self, schema) -> None:
        super().__init__('loiter', schema)

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


class DistanceBasedGoToGenerator(ActionGenerator):
    """
    This action generator uses its knowledge of the system state to generate
    GoTo actions that will take the robot a given distance along a certain
    heading.
    """
    def __init__(self,
                 max_distance: float,
                 min_distance: float = 1.0
                 ) -> None:
        assert max_distance > min_distance
        assert min_distance > 0.0
        self.__max_distance = max_distance
        parameters = [
            Parameter('distance',
                      ContinuousValueRange(min_distance, max_distance)),
            Parameter('heading',
                      ContinuousValueRange(0.0, 360.0, True))]
        super().__init__('goto', parameters)

    def construct_with_state(self, current_state, env, config, values):
        dist = values['distance']
        heading = values['heading']
        lon = current_state.longitude
        lat = current_state.latitude
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination = dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = current_state.altitude

        return params

    def construct_without_state(self, env, config, values):
        raise NotImplementedError


class CircleBasedGotoGenerator(ActionGenerator):
    def __init__(self,
                 centre_coords: Tuple[float, float],
                 radius: float
                 ) -> None:
        self.__centre_coords = centre_coords
        parameters = [
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super().__init__('goto', parameters)

    def construct_without_state(self, env, config, values):
        (lat, lon) = self.__centre_coords
        heading = values['heading']
        dist = values['distance']
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination = dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        # FIXME small limitation since we don't have current
        # state to get altitude.
        params['altitude'] = 10.0

        return params

    def construct_with_state(self, current_state, env, config, values):
        return self.construct_without_state(env, config, values)
