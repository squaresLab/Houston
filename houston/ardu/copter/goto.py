import time
import math
import geopy
import geopy.distance

from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.valueRange import ContinuousValueRange, DiscreteValueRange
from houston.ardu.common.goto import DistanceBasedGoToGenerator, \
                                     CircleBasedGotoGenerator, \
                                     GotoLoiter


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
