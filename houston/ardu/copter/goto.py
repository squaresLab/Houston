import time
import math
import geopy
import geopy.distance

from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.valueRange import ContinuousValueRange, DiscreteValueRange


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
        import dronekit
        loc = dronekit.LocationGlobalRelative(action['latitude'],
                                              action['longitude'],
                                              action['altitude'])
        system.vehicle.simple_goto(loc)


class GotoNormally(Branch):
    def __init__(self, system):
        super(GotoNormally, self).__init__('normal', system)


    def timeout(self, system, action, state, environment):
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (action['latitude'], action['longitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters
        timeout = dist * system.time_per_metre_travelled
        timeout += system.constant_timeout_offset
        return timeout

    
    def precondition(self, system, action, state, environment):
        return  state['armed'] and \
                state['mode'] != 'LOITER' and \
                system.variable('altitude').gt(state['altitude'], 0.3)


    def postcondition(self, system, action, state_before, state_after, environment):
        return  system.variable('longitude').eq(state_after['longitude'], action['longitude']) and \
                system.variable('latitude').eq(state_after['latitude'], action['latitude']) and \
                system.variable('altitude').eq(state_after['altitude'], action['altitude'])


    def is_satisfiable(self, system, state, environment):
        return self.precondition(system, None, state, environment)


    def generate(self, state, environment, rng):
        return self.schema.generate(rng)


class GotoLoiter(Branch):
    def __init__(self, system):
        super(GotoLoiter, self).__init__('loiter', system)


    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset


    def precondition(self, system, action, state, environment):
        return  state['armed'] and \
                state['mode'] == 'LOITER' and \
                system.variables('altitude').eq(state['altitude'], 0.3)


    def postcondition(self, system, action, state_before, state_after, environment):
        return  state_after['mode'] == 'LOITER' and \
                system.variables('longitude').eq(state_after['longitude'], state_before['longitude']) and \
                system.variables('latitude').eq(state_after['latitude'], state_before['latitude']) and \
                system.variables('altitude').eq(state_after['altitude'], state_before['altitude'])


    def is_satisfiable(self, system, state, environment):
        return self.precondition(system, None, state, environment)


    def generate(self, system, state, environment, rng):
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


    def construct_with_state(self, system, current_state, env, values):
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


    def construct_without_state(self, system, env, values):
        raise NotImplementedError


class CircleBasedGotoGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, centre_coords, radius):
        assert isinstance(centre_coords, tuple)
        assert isinstance(radius, float)
        self.__centre_coords = centre_coords
        self.__radius = radius

        parameters = [
            Parameter('latitude', DiscreteValueRange([centre_coords[0]])),
            Parameter('longitude', DiscreteValueRange([centre_coords[1]])),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super(CircleBasedGotoGenerator, self).__init__('goto', parameters)


    def construct_without_state(self, system, env, values):
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


    def construct_with_state(self, system, current_state, env, values):
        return self.construct_without_state(system, env, values)
