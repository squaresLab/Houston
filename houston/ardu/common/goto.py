from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.valueRange import ContinuousValueRange, DiscreteValueRange
from houston.branch import Branch, IdleBranch


class GotoLoiter(Branch):
    """
    If the robot is armed and in its `LOITER` mode, GoTo actions should have no
    effect upon the robot. (Why isn't this covered by Idle?)
    """
    def __init__(self, system):
        super(GotoLoiter, self).__init__('loiter', system)


    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset


    def precondition(self, system, action, state, environment):
        return  state['armed'] and state['mode'] == 'LOITER'


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
    This action generator uses its knowledge of the system state to generate
    GoTo actions that will take the robot a given distance along a certain
    heading.
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

        parameters = [
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super(CircleBasedGotoGenerator, self).__init__('goto', parameters)


    def construct_without_state(self, system, env, values):
        (lat, lon) = self.__centre_coords
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
