import time

from houston.ardu.base import CONSTANT_TIMEOUT_OFFSET
from houston.action import ActionSchema, Parameter, Action
from houston.branch import Branch, IdleBranch
from houston.state import Estimator, FixedEstimator
from houston.valueRange import DiscreteValueRange


class SetModeSchema(ActionSchema):
    """
    docstring for SetModeActionSchema

    Branches:

        Guided:
        Loiter:
        RTL:
        Land:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('mode', DiscreteValueRange(['GUIDED', 'LOITER', 'RTL', 'LAND']))
        ]
        branches = [
            SetModeGuided(self),
            SetModeLoiter(self),
            SetModeRTL(self),
            SetModeLand(self),
            IdleBranch(self)
        ]

        super(SetModeSchema, self).__init__('setmode', parameters, branches)


    def dispatch(self, system, action, state, environment):
        vehicle = system.vehicle
        msg = ({
            'RTL': mavutil.mavlink.MAV_CMD_NAV_RETURN_TO_LAUNCH,
            'LAND': mavutil.mavlink.MAV_CMD_NAV_LAND,
            'LOITER': mavutil.mavlink.MAV_CMD_NAV_LOITER_UNLIM
        })[action['mode']]
        msg = \
            vehicle.message_factory.command_long_encode(0, 0, msg, 0, 0, 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)
        

class SetModeLand(Branch):
    def timeout(self, action, state, environment):
        timeout = (state['altitude'] * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def postcondition(self, action, state_before, state_after, environment):
        return  state_after['mode'] == 'LAND' and \
                state_after['armed'] == False and \
                state_after['latitude'] == state_before['latitude'] and \
                state_after['longitude'] == state_before['longitude'] and \
                state_after['altitude'] == 0.0


    def precondition(self, action, state, environment):
        return action['mode'] == 'LAND'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'LAND'})


class SetModeGuided(Branch):
    def timeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def postcondition(self, action, state_before, state_after, environment):
        return state_after['mode'] == 'GUIDED'


    def precondition(self, action, state, environment):
        return action['mode'] == 'GUIDED'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'GUIDED'})


class SetModeLoiter(Branch):
    def timeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET

    
    def postcondition(self, action, state_before, state_after, environment):
        return state_after['mode'] == 'LOITER'


    def precondition(self, action, state, environment):
        return action['mode'] != 'LOITER'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'LOITER'})


class SetModeRTL(Branch):
    """
    Description.
    """
    def timeout(self, action, state, environment):
        # compute distance
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (state['homeLatitude'], state['homeLongitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters

        # compute time taken to travel from A to B, and time taken to land
        time_goto_phase = dist * TIME_PER_METER_TRAVELED
        time_land_phase = state['altitude'] * TIME_PER_METER_TRAVELED

        # TODO: what was this? No explanation of logic?
        # Land times and adjustment time for altitude
        #total_go_up_down_time = \
        #    math.fabs(10 - state['altitude']) * TIME_PER_METER_TRAVELED

        # compute total timeout
        timeout = time_goto_phase + time_land_phase
        return timeout


    def postcondition(self, action, state_before, state_after, environment):
        if state_after['mode'] != 'RTL':
            return False # hmmm?

        if state_before['altitude'] < 0.3:
            if state_before['armed'] != state_after['armed']:
                return False
        else:
            if state_before['armed'] != False:
                return False

        # vars['altitude'].equal(0.0, state['altitude'])
        # vars['latitude'].equal(state['homeLatitude'], state['latitude'])
        # vars['longitude'].equal(state['homeLongitude'], state['longitude'])


        return True


    def precondition(self, action, state, environment):
        return action['mode'] == 'RTL'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'RTL'})
