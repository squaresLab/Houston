import time

from houston.action import ActionSchema, Parameter, Action
from houston.branch import Branch, IdleBranch
from houston.state import Estimator, FixedEstimator
from houston.valueRange import DiscreteValueRange


try:
    import dronekit
except ImportError:
    pass


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

    # theseusend commands are all almost identical?    
    def send_RTL(self, vehicle):
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_RETURN_TO_LAUNCH,
            0,
            0,
            0,
            0,
            0,
            0, 0, 0)
        vehicle.send_mavlink(msg)


    def send_LAND(self, vehicle):
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_LAND,
            0,
            0,
            0,
            0,
            0,
            0, 0, 0)
        vehicle.send_mavlink(msg)


    def send_LOITER(self, vehicle):
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_LOITER_UNLIM,
            0,    #confirmation
            0,    # param 1
            0,    # param 2,
            0,    # param 3,
            0,    # param 4,
            0, 0, 0)    # param 5 ~ 7 not used
            # send command to vehicle
        vehicle.send_mavlink(msg)


    def dispatch(self, system, action, state, environment):
        vehicle = system.vehicle
        vehicle_mode = dronekit.VehicleMode(action['mode'])

        if action['mode'] == 'RTL':
            self.send_RTL(vehicle)
            while not vehicle.mode == vehicle_mode:
                time.sleep(0.2)

            to_loc = (state['homeLatitude'], state['homeLongitude'])
            while True:
                current_alt = vehicle.location.global_relative_frame.alt
                current_lat = vehicle.location.global_relative_frame.lat
                current_lon = vehicle.location.global_relative_frame.lon
                current_loc = (current_lat, current_lon)

                dist = geopy.distance.great_circle(from_location, to_location)
                if dist.meters <= 0.3 and current_alt <= 0.1:
                    break

                time.sleep(0.2)

            # block until vehicle is no longer armed
            while vehicle.armed:
                time.sleep(0.2)

        elif action['mode'] == 'LAND':
            self.send_LAND(vehicle)

            # block until mode change is acknowledged
            while not vehicle.mode == vehicle_mode:
                time.sleep(0.2)

            # block until altitude is <= 0.1
            while True:
                current_alt = vehicle.location.global_relative_frame.alt
                if current_alt <= 0.1:
                    break
                time.sleep(0.2)
        
            # block until vehicle is no longer armed
            while vehicle.armed:
                time.sleep(0.2)

        elif action['mode'] == 'LOITER': # TODO as we add more modes this would have to change
            self.send_LOITER(vehicle)

            # block until mode change is acknowledged
            while not vehicle.mode == vehicle_mode:
                time.sleep(0.1)

        elif action['mode'] == 'GUIDED':
            vehicle.mode = vehicleMode

            # block until mode change is acknowledged
            while not vehicle.mode == vehicle_mode:
                time.sleep(0.1)

        else:
            raise Exception("unexpected mode")


class SetModeLand(Branch):
    """
    Should describe precondition, postcondition, invariants, and method for
    calculating a suitable timeout.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'LAND'),
            FixedEstimator('armed', False),
            Estimator('latitude', lambda action, state, env: state['latitude']),
            Estimator('longitude', lambda action, state, env: state['longitude']),
            Estimator('altitude', lambda action, state, env: 0.0)
        ]
        super(SetModeLand, self).__init__('land', schema, estimators)


    def compute_timeout(self, action, state, environment):
        timeout = (state['altitude'] * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def is_applicable(self, action, state, environment):
        return action['mode'] == 'LAND'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'LAND'})


class SetModeGuided(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'GUIDED')
        ]
        super(SetModeGuided, self).__init__('guided', schema, estimators)


    def compute_timeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def is_applicable(self, action, state, environment):
        return action['mode'] == 'GUIDED'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'GUIDED'})



class SetModeLoiter(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'LOITER')
        ]
        super(SetModeLoiter, self).__init__('loiter', schema, estimators)


    def compute_timeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def is_applicable(self, action, state, environment):
        return action['mode'] == 'LOITER'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'LOITER'})


class SetModeRTL(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'RTL'),
            Estimator('armed', \
                      lambda action, state, env: state['armed'] if state['altitude'] < 0.3 else False),
            Estimator('latitude', \
                      lambda action, state, env: state['homeLatitude']),
            Estimator('longitude', \
                      lambda action, state, env: state['homeLongitude']),
            Estimator('altitude', \
                      lambda action, state, env: 0.0)
        ]
        super(SetModeRTL, self).__init__('rtl', schema, estimators)


    def compute_timeout(self, action, state, environment):
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


    def is_applicable(self, action, state, environment):
        return action['mode'] == 'RTL'


    def is_satisfiable(self, state, environment):
        return True


    def generate(self, state, environment, rng):
        return Action(self.schema_name, {'mode': 'RTL'})
