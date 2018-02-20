import dronekit
from houston.state import Environment, State
from houston.action import Action, ActionSchema, Parameter
from houston.branch import IdleBranch
from houston.valueRange import ContinuousValueRange, DiscreteValueRange
from houston.ardu.common.goto import DistanceBasedGoToGenerator, \
                                     CircleBasedGotoGenerator, \
                                     GotoNormally, \
                                     GotoLoiter


class GoToSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True))
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
                                              state['altitude'])
        system.vehicle.simple_goto(loc)
