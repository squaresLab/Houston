import time

import dronekit
import geopy

from ...state import State, Environment
from ...action import ActionSchema, Parameter, Action
from ...branch import Branch, IdleBranch
from ...valueRange import DiscreteValueRange


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
        branches = [
            SetModeGuided(self),
            SetModeLoiter(self),
            SetModeRTL(self),
            SetModeLand(self),
            IdleBranch(self)
        ]
        super(SetModeSchema, self).__init__('setmode', parameters, branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment
                 ) -> None:
        sandbox.connection.mode = dronekit.VehicleMode(action['mode'])


class SetModeLand(Branch):
    def __init__(self, system):
        super(SetModeLand, self).__init__('land', system)

    def timeout(self, system, action, state, environment):
        timeout = state['altitude'] * system.time_per_metre_travelled
        timeout += system.constant_timeout_offset
        return timeout

    def postcondition(self,
                      system,
                      action,
                      state_before,
                      state_after,
                      environment):
        v = system.variable
        sat_mode = state_after['mode'] == 'LAND'
        sat_lon = \
            v('longitude').eq(state_after['longitude'],
                              state_before['longitude'])
        sat_lat = \
            v('latitude').eq(state_after['latitude'], state_before['latitude'])
        sat_alt = v('altitude').eq(state_after['altitude'], 0.0)

    def precondition(self, system, action, state, environment):
        return action['mode'] == 'LAND' and state['altitude'] > 0.3

    def is_satisfiable(self, system, state, environment):
        return state['altitude'] > 0.3

    def generate(self, system, state, environment, rng):
        return Action(self.schema.name, {'mode': 'LAND'})


class SetModeGuided(Branch):
    def __init__(self, system):
        super(SetModeGuided, self).__init__('guided', system)

    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset

    def postcondition(self,
                      system,
                      action,
                      state_before,
                      state_after,
                      environment):
        return state_after['mode'] == 'GUIDED'

    def precondition(self, system, action, state, environment):
        return action['mode'] == 'GUIDED'

    def is_satisfiable(self, system, state, environment):
        return True

    def generate(self, system, state, environment, rng):
        return Action(self.schema.name, {'mode': 'GUIDED'})


class SetModeLoiter(Branch):
    def __init__(self, system):
        super(SetModeLoiter, self).__init__('loiter', system)

    def timeout(self, system, action, state, environment):
        return system.constant_timeout_offset

    def postcondition(self,
                      system,
                      action,
                      state_before,
                      state_after,
                      environment):
        return state_after['mode'] == 'LOITER'

    def precondition(self, system, action, state, environment):
        return action['mode'] == 'LOITER'

    def is_satisfiable(self, system, state, environment):
        return True

    def generate(self, system, state, environment, rng):
        return Action(self.schema.name, {'mode': 'LOITER'})


class SetModeRTL(Branch):
    def __init__(self, system):
        super(SetModeRTL, self).__init__('rtl', system)

    def timeout(self, system, action, state, environment):
        # compute distance
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (state['homeLatitude'], state['homeLongitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters

        # compute time taken to travel from A to B, and time taken to land
        time_goto_phase = dist * system.time_per_metre_travelled
        time_land_phase = state['altitude'] * system.time_per_metre_travelled

        # TODO: what was this? No explanation of logic?
        # Land times and adjustment time for altitude
        # total_go_up_down_time = \
        #    math.fabs(10 - state['altitude']) *
        # system.time_per_metre_travelled

        # compute total timeout
        timeout = \
            time_goto_phase + time_land_phase + system.constant_timeout_offset

        print('calculated timeout: {} seconds'.format(timeout))
        return timeout

    def postcondition(self,
                      system,
                      action,
                      state_before,
                      state_after,
                      environment):
        v = system.variable
        if state_after['mode'] != 'RTL':
            return False  # hmmm?

        if state_before['altitude'] < 0.3:
            if state_before['armed'] != state_after['armed']:
                return False
        elif state_before['armed']:
            return False

        sat_alt = v('altitude').eq(state_after['altitude'], 0.0)
        sat_lat = v('latitude').eq(state_after['latitude'],
                                   state_before['homeLatitude'])
        sat_lon = v('longitude').eq(state_after['longitude'],
                                    state_before['homeLongitude'])

        return sat_alt and sat_lat and sat_lon

    def precondition(self, system, action, state, environment):
        return action['mode'] == 'RTL'

    def is_satisfiable(self, system, state, environment):
        return True

    def generate(self, system, state, environment, rng):
        return Action(self.schema.name, {'mode': 'RTL'})
