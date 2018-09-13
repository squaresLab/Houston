__all__ = ['GoToSchema', 'GotoNormally']

import dronekit
import geopy

from ..common.goto import GotoNormally as GotoNormallyBase
from ..common.goto import DistanceBasedGoToGenerator, \
    CircleBasedGotoGenerator, \
    GotoLoiter
from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...action import Action, ActionSchema, Parameter
from ...branch import IdleBranch, Branch
from ...valueRange import ContinuousValueRange, DiscreteValueRange


class GoToSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
            Parameter('altitude', ContinuousValueRange(0.3, 100.0))
        ]

        branches = [
            GotoNormally(self, parameters),
            GotoLoiter(self, parameters),
            IdleBranch(self, parameters)
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


class GotoNormally(Branch):

    def __init__(self, schema, parameters):
        specification = Specification(parameters,
            """
            (and (= _armed true)
                (not (= _mode "LOITER"))
                (> _altitude 0.3))
            """,
            """
            (and (= __longitude $longitude)
                (= __latitude $latitude)
                (= __altitude $altitude))
            """,
            None)
        super(GotoNormally, self).__init__('normal', schema, specification)
    
    def timeout(self, system, action, state, environment):
        from_loc = (state['latitude'], state['longitude'])
        to_loc = (action['latitude'], action['longitude'])
        dist = geopy.distance.great_circle(from_loc, to_loc).meters
        timeout = dist * system.time_per_metre_travelled
        timeout += system.constant_timeout_offset
        return timeout

