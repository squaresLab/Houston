__all__ = ['GotoLoiter']

from typing import Tuple

import geopy
import geopy.distance

from ...state import State
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...valueRange import ContinuousValueRange, DiscreteValueRange
from ...specification import Specification, Idle


class GotoLoiter(Specification):
    """
    If the robot is armed and in its `LOITER` mode, GoTo actions should have no
    effect upon the robot. (Why isn't this covered by Idle?)
    """
    def __init__(self) -> None:
        pre = lambda a, s, e, c: s.armed and s.mode == 'LOITER'
        timeout = lambda a, s, e, c: c.constant_timeout_offset

        def post(a, s0, s1, e, c) -> bool:
            sat_mode = s1.mode == 'LOITER'
            # FIXME 82
            err_lon = 0.1
            err_lat = 0.1
            err_alt = 0.5
            sat_lon = abs(s1.longitude - s0.longitude) <= err_lon
            sat_lat = abs(s1.latitude - s0.latitude) <= err_lat
            sat_alt = abs(s1.altitude - s0.altitude) <= err_alt
            return sat_mode and sat_lon and sat_lat and sat_alt

        super().__init__('loiter', pre, post, timeout)
