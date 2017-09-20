import time
import math
import geopy
import geopy.distance

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
            IdleBranch(self)
        ]

        super(GoToSchema, self).__init__('goto', parameters, branches)


    def dispatch(self, system, action, state, environment):
        vehicle = system.vehicle
        vehicle.simple_goto(LocationGlobalRelative(
            action['latitude'],
            action['longitude'],
            action['altitude'])
        )

        # block until (lat, lon) is reached
        to_loc = (action['latitude'], action['longitude'])
        while True:
            current_lat  = vehicle.location.global_relative_frame.lat
            current_lon = vehicle.location.global_relative_frame.lon
            current_loc = (current_lat, current_lon)
            dist = geopy.distance.great_circle(current_loc, to_loc)
            if dist.meters <= 0.3:
                break

        # block until altitude has reached a threshold
        while True:
            current_alt = vehicle.location.global_relative_frame.alt
            if math.fabs(current_alt - action['altitude']) > 0.3:
                break
            time.sleep(0.2)


class GotoNormally(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('latitude', \
                      lambda action, state, env: state['latitude'] if state['mode'] == 'LOITER' else action['latitude']),
            Estimator('longitude', \
                      lambda action, state, env: state['longitude'] if state['mode'] == 'LOITER' else action.read['longitude']),
            Estimator('altitude', \
                      lambda action, state, env: 0.0 if state['mode'] == 'LOITER' else action['altitude'])
        ]
        super(GotoNormally, self).__init__('normal', schema, estimators)


    def compute_timeout(self, action, state, environment):
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (action['latitude'], action['longitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters
        timeout = (dist * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def is_applicable(self, action, state, environment):
        return state['armed'] and state['altitude'] > 0.3


    def is_satisfiable(self, state, environment):
        return self.is_applicable(None, state, environment)


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
