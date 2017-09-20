import time
import math
import geopy
import geopy.distance

from houston.ardu.base import CONSTANT_TIMEOUT_OFFSET
from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.state import Estimator, FixedEstimator
from houston.valueRange import ContinuousValueRange, DiscreteValueRange

try:
    from dronekit import LocationGlobalRelative
except ImportError:
    pass


class GoToSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]

        branches = [
            GotoNormally(self),
            GotoLoiter(self),
            IdleBranch(self)
        ]

        super(GoToSchema, self).__init__('goto', parameters, branches)


    def dispatch(self, system, action, state, environment):
        loc = LocationGlobalRelative(action['latitude'],
                                     action['longitude'],
                                     action['altitude'])
        system.vehicle.simple_goto(loc)


class GotoNormally(Branch):
    """
    Description.
    """
    def timeout(self, action, state, environment):
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (action['latitude'], action['longitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters
        timeout = (dist * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout

    
    def precondition(self, action, state, environment):
        return  state['armed'] and \
                state['altitude'] > 0.3 and \
                state['mode'] != 'LOITER'


    def postcondition(self, action, state_before, state_after, environment):
        return  state_after['longitude'].eq(action['longitude']) and \
                state_after['latitude'].eq(action['latitude']) and \
                state_after['altitude'].eq(action['altitude'])


    def is_satisfiable(self, state, environment):
        return self.precondition(None, state, environment)


    def generate(self, state, environment, rng):
        return self.schema.generate(rng)


class GotoLoiter(Branch):
    def timeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def precondition(self, action, state, environment):
        return state['armed'] and state['altitude'] > 0.3 and state['mode'] == 'LOITER'


    def postcondition(self, action, state_before, state_after, environment):
        return  state_after['mode'] == 'LOITER' and \
                state_after['longitude'] == state_before['longitude'] and \
                state_after['latitude'] == state_before['latitude'] and \
                state_after['altitude'] == state_before['altitude']


    def is_satisfiable(self, state, environment):
        return self.precondition(None, state, environment)



    def generate(self, state, environment, rng):
        return self.schema.generate(rng)


class DistanceBasedGoToGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, max_distance, min_distance = 1.0):
        assert isinstance(max_distance, float)
        assert isinstance(min_distance, float)
        assert (max_distance > min_distance)
        assert (min_distance > 0.0)

        self.__max_distance = max_distance
        parameters = [
            Parameter('distance', ContinuousValueRange(min_distance, max_distance)),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True))
        ]

        super(DistanceBasedGoToGenerator, self).__init__('goto', parameters)


    def construct_with_state(self, current_state, env, values):
        dist = values['distance']
        heading = values['heading']
        lon = current_state['longitude']
        lat = current_state['latitude']
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination =  dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = current_state['altitude']

        return params


    def construct_without_state(self, env, values):
        raise NotImplementedError


class CircleBasedGotoGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, centre_coords, radius):
        assert isinstance(centre_coords, tuple)
        assert isinstance(radius, float)
        self.__center_coords = center_coords
        self.__radius = radius

        parameters = [
            Parameter('latitude', DiscreteValueRange([center_coords[0]])),
            Parameter('longitude', DiscreteValueRange([center_coords[1]])),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super(CircleBasedGotoGenerator, self).__init__('goto', parameters)


    def construct_without_state(self, env, values):
        lat = values['latitude']
        lon = values['longitude']
        heading = values['heading']
        dist = values['distance']
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination =  dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = 10.0 # small limitation since we don't have current
                                  # state to get altitude.

        return params


    def construct_with_state(self, current_state, env, values):
        return self.construct_without_state(env, values)
