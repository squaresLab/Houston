import arm

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


    def dispatch(self, system, action, state, environment):
        vehicle = system.getVehicle()
        msg = vehicle.message_factory.command_long_encode(
            0, 0,    # target_system, target_component
            mavutil.mavlink.MAV_CMD_COMPONENT_ARM_DISARM,
            0,
            1,
            0,
            0,
            0,
            0, 0, 0)
        vehicle.send_mavlink(msg)

        # TODO: why aren't we using "DRONEKIT_SYSTEM.armed = True"?
        while not vehicle.armed:
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
