__all__ = ['GoToSchema']

import dronekit

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...action import Action, ActionSchema, Parameter
from ...branch import IdleBranch
from ...valueRange import ContinuousValueRange, DiscreteValueRange
from ..common.goto import GotoNormally, GotoLoiter


class GoToSchema(ActionSchema):
    def __init__(self) -> None:
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True))
        ]
        branches = [
            GotoNormally(),
            GotoLoiter(),
            IdleBranch()
        ]
        super().__init__('goto', parameters, branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        loc = dronekit.LocationGlobalRelative(action['latitude'],
                                              action['longitude'],
                                              state['altitude'])
        sandbox.connection.simple_goto(loc)
