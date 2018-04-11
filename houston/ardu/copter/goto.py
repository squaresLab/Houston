import dronekit
import houston.ardu.common.goto
from houston.state import Environment, State
from houston.action import Action, ActionSchema, Parameter
from houston.branch import IdleBranch
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

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment
                 ) -> None:
        loc = dronekit.LocationGlobalRelative(action['latitude'],
                                              action['longitude'],
                                              action['altitude'])
        sandbox.connection.simple_goto(loc)


class GotoNormally(houston.ardu.common.goto.GotoNormally):
    def precondition(self, system, action, state, environment):
        """
        For GoTo actions within the ArduCopter to exhibit a "normal" behaviour,
        the robot must be at an altitude greater than 0.3 metres.
        """
        if not super(GotoNormally, self).precondition(system, action, state, environment):
            return False
        return system.variable('altitude').gt(state['altitude'], 0.3)

    def postcondition(self, system, action, state_before, state_after, environment):
        """
        Upon completion of the action, the robot should be at the longitude,
        latitude, and altitude specified by the action.
        """
        if not super(GotoNormally, self).postcondition(system, action, state_before, state_after, environment):
            return False
        return system.variable('altitude').eq(state_after['altitude'], action['altitude'])
