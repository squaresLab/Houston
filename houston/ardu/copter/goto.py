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
        vehicle = system.getVehicle()
        vehicle.simple_goto(LocationGlobalRelative(
            action.read('latitude'),
            action.read('longitude'),
            action.read('altitude'))
        )
        currentLat  = vehicle.location.global_relative_frame.lat
        currentLon = vehicle.location.global_relative_frame.lon
        toLocation = (action.getValue('latitude'), action.getValue('longitude'))
        fromLocation = (currentLat, currentLon)

        while geopy.distance.great_circle(fromLocation, toLocation).meters > 0.3:
            time.sleep(0.2)
            currentLat  = vehicle.location.global_relative_frame.lat
            currentLon = vehicle.location.global_relative_frame.lon

        while math.fabs(currentAlt - action.read('altitude')) > 0.3:
            time.sleep(0.2)
            currentAlt = vehicle.location.global_relative_frame.alt


class GotoNormally(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('latitude', lambda action, state, env: state.read('latitude') if state.read('mode') == 'LOITER' else action.read('latitude')),
            Estimator('longitude', lambda action, state, env: state.read('longitude') if state.read('mode') == 'LOITER' else action.read('longitude')),
            Estimator('altitude', lambda action, state, env: 0.0 if state.read('mode') == 'LOITER' else action.read('altitude'))
        ]
        super(GotoNormally, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        fromLocation = (state.read('latitude'), state.read('longitude'))
        toLocation   = (action.getValue('latitude'), action.getValue('longitude'))
        totalDistance = geopy.distance.great_circle(fromLocation, toLocation).meters
        timeout = (totalDistance * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def isApplicable(self, action, state, environment):
        return state.read('armed') and state.read('altitude') > 0.3


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)


    def generate(self, state, environment, rng):
        return self.getSchema().generate(rng)


class DistanceBasedGoToGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, maxDistance, minDistance = 1.0):
        assert (isinstance(maxDistance, float) and maxDistance is not None)
        assert (isinstance(minDistance, float) and minDistance is not None)
        assert (maxDistance > minDistance)
        assert (minDistance > 0.0)

        self.__maxDistance = maxDistance
        parameters = [
            Parameter('distance', ContinuousValueRange(minDistance, maxDistance)),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True))
        ]

        super(DistanceBasedGoToGenerator, self).__init__('goto', parameters)


    def constructWithState(self, currentState, env, values):
        dist = values['distance']
        heading = values['heading']
        lon = currentState.read('longitude')
        lat = currentState.read('latitude')
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination =  dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = currentState.read('altitude')

        return params


    def constructWithoutState(self, env, values):
        raise NotImplementedError


class CircleBasedGotoGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, centerCoordinates, radius):
        assert (isinstance(centerCoordinates, tuple) and centerCoordinates is not None)
        assert (isinstance(radius, float) and radius is not None)
        self.__centerCoordinates = centerCoordinates
        self.__radius = radius

        parameters = [
            Parameter('latitude', DiscreteValueRange([centerCoordinates[0]])),
            Parameter('longitude', DiscreteValueRange([centerCoordinates[1]])),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super(CircleBasedGotoGenerator, self).__init__('goto', parameters)


    def constructWithoutState(self, env, values):
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


    def constructWithState(self, currentState, env, values):
        return self.constructWithoutState(env, values)
