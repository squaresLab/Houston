__all__ = ['GoToSchema', 'GotoNormally']

import dronekit

from ..common.goto import GotoNormally as GotoNormallyBase
from ..common.goto import DistanceBasedGoToGenerator, \
    CircleBasedGotoGenerator, \
    GotoLoiter
from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...action import Action, ActionSchema, Parameter
from ...branch import IdleBranch
from ...valueRange import ContinuousValueRange, DiscreteValueRange


class GoToSchema(ActionSchema):
    def __init__(self) -> None:
        name = 'goto'
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]
        branches = [
            GotoNormally(),
            GotoLoiter(),
            IdleBranch()
        ]
        super().__init__(name, parameters, branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        loc = dronekit.LocationGlobalRelative(action['latitude'],
                                              action['longitude'],
                                              action['altitude'])
        sandbox.connection.simple_goto(loc)


class GotoNormally(GotoNormallyBase):
    def precondition(self, action, state, environment, config) -> bool:
        """
        For GoTo actions within the ArduCopter to exhibit a "normal" behaviour,
        the robot must be at an altitude greater than 0.3 metres.
        """
        base = super().precondition(action, state, environment, config)
        if not base:
            return False
        # FIXME 82
        err_alt = 0.1
        sat_alt = state.altitude + err_alt > 0.3
        return sat_alt

    def postcondition(self,
                      action,
                      state_before,
                      state_after,
                      environment,
                      config) -> bool:
        """
        Upon completion of the action, the robot should be at the longitude,
        latitude, and altitude specified by the action.
        """
        base = super().postcondition(action, state_before, state_after,
                                     environment, config)
        if not base:
            return False
        # FIXME 82
        err_alt = 0.1
        sat_alt = abs(state_after.altitude - action['altitude']) <= err_alt
        return sat_alt
