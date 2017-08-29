from houton.action import ActionSchema, Parameter, Action
from houston.branch import Branch
from houston.state import Estimator, FixedEstimator
from houston.util import DiscreteValueRange


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


    def dispatch(self, action, state, environment):
        msg = DRONEKIT_SYSTEM.message_factory.command_long_encode(
            0, 0,    # target_system, target_component
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF, #command
            0,    #confirmation
            1,    # param 1
            0,    # param 2,
            0,    # param 3,
            0,    # param 4,
            0, 0, action.read('altitude'))    # param 5 ~ 7 not used
            # send command to vehicle
        DRONEKIT_SYSTEM.send_mavlink(msg)

        expectedAlt = action.read('altitude')
        currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt

        while currentAlt < expectedAlt - 0.3: # OFFSET
            time.sleep(.1)
            currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt


class TakeoffNormally(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('altitude', lambda action, state, env: action.read('altitude'))
        ]
        super(TakeoffNormally, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        timeout = (action.read('altitude') * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def isApplicable(self, action, state, environment):
        return state.read('armed') and state.read('altitude') < 0.3 and state.read('mode') == 'GUIDED' #TODO further check


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)

    def generate(self, initialState, env, rng):
        return self.getSchema().generate(rng)
