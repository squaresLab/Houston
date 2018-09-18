__all__ = ['GoToSchema']

import dronekit

from ...configuration import Configuration
from ...state import State
from ...environment import Environment
from ...action import Action, ActionSchema, Parameter
from ...specification import Idle, Specification
from ...valueRange import ContinuousValueRange, DiscreteValueRange
from ..common.goto import GotoLoiter


class GotoNormally(Specification):
    """
    If the robot is armed and not in its `LOITER` mode, GoTo actions should
    cause the robot to move to the desired location. For certain Ardu systems,
    the precondition on this normal behaviour is stronger; for more
    information, refer to the system-specific subclasses of GotoNormally.
    """
    def __init__(self) -> None:
        pre = lambda a, s, e, c: s.armed and s.mode != 'LOITER'

        def post(a, s0, s1, e, c) -> bool:
            err_lon = 0.1
            err_lat = 0.1
            sat_lon = abs(s1.longitude - a['longitude']) <= err_lon
            sat_lat = abs(s1.latitude - a['latitude']) <= err_lat
            return sat_lon and sat_lat

        def timeout(a, s, e, c) -> float:
            from_loc = (s.latitude, s.longitude)
            to_loc = (a['latitude'], a['longitude'])
            dist = geopy.distance.great_circle(from_loc, to_loc).meters
            timeout = dist * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__('normal', pre, post, timeout)


class GoToSchema(ActionSchema):
    def __init__(self) -> None:
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True))
        ]
        specs = [
            GotoNormally(),
            GotoLoiter(),
            Idle()
        ]
        super().__init__('goto', parameters, specs)

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
