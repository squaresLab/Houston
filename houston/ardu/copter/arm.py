from houston.action import ActionSchema, Parameter, Action, ActionGenerator
from houston.branch import Branch, IdleBranch
from houston.state import Estimator, FixedEstimator
from houston.valueRange import DiscreteValueRange


class ArmSchema(ActionSchema):
    """
    TODO: docstring
    
    Behaviours:
   
        Normal: if the robot is armable and it is in either its 'GUIDED' or
            'LOITER' modes, the robot will become armed.
        Idle: if the conditions above cannot be met, the robot will ignore the
            command.
    """
    def __init__(self):
        parameters = []
        branches = [
            ArmNormally(self),
            IdleBranch(self)
        ]
        super(ArmSchema, self).__init__('arm', parameters, branches)


    def dispatch(self, action, state, environment):
        msg = DRONEKIT_SYSTEM.message_factory.command_long_encode(
            0, 0,    # target_system, target_component
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM, #command
            0,    #confirmation
            1,    # param 1
            0,    # param 2,
            0,    # param 3,
            0,    # param 4,
            0, 0, 0)    # param 5 ~ 7 not used
            # send command to vehicle
        DRONEKIT_SYSTEM.send_mavlink(msg)

        #DRONEKIT_SYSTEM.armed = True
        while not DRONEKIT_SYSTEM.armed:
            time.sleep(0.1)


class ArmNormally(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('armed', True)
        ]
        super(ArmNormally, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def isApplicable(self, action, state, environment):
        return state.read('armable') and (state.read('mode') == 'GUIDED' or state.read('mode') == 'LOITER')


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)


    def generate(self, state, environment, rng):
        return self.getSchema().generate(rng)
