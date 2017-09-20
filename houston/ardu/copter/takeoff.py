import time
import math

from houston.action import ActionSchema, Parameter, Action
from houston.branch import Branch, IdleBranch
from houston.state import Estimator, FixedEstimator
from houston.valueRange import ContinuousValueRange

try:
    import dronekit
except ImportError:
    pass


class TakeoffSchema(ActionSchema):
    """docstring for TakeoffActionSchema.
    
    Branches:
        Normally:
        Idle:
    """
    def __init__(self):
        parameters = [
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]
        branches = [
            TakeoffNormally(self),
            IdleBranch(self)
        ]

        super(TakeoffSchema, self).__init__('takeoff', parameters, branches)


    def dispatch(self, system, action, state, environment):
        vehicle = system.vehicle
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF,
            0, 1, 0, 0, 0, 0, 0, action['altitude'])
        vehicle.send_mavlink(msg)

        expected_alt = action['altitude']
        current_alt = vehicle.location.global_relative_frame.alt
        while math.fabs(current_alt - expected_alt) > 0.3:
            time.sleep(0.1)
            currentAlt = vehicle.location.global_relative_frame.alt


class TakeoffNormally(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('altitude', lambda action, state, env: action['altitude'])
        ]
        super(TakeoffNormally, self).__init__('normal', schema, estimators)


    def compute_timeout(self, action, state, environment):
        timeout = (action['altitude'] * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def is_applicable(self, action, state, environment):
        return state['armed'] and state['altitude'] < 0.3 and state['mode'] == 'GUIDED' #TODO further check; CT: for what?


    def is_satisfiable(self, state, environment):
        return self.is_applicable(None, state, environment)

    def generate(self, initialState, env, rng):
        return self.schema.generate(rng)
