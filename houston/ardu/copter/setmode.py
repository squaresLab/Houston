__all__ = ['SetMode']

import time
import logging

import dronekit
import geopy

from ...configuration import Configuration
from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...command import Parameter, Command
from ...specification import Specification, Idle
from ...valueRange import DiscreteValueRange

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class SetModeLand(Specification):
    def __init__(self):
        def timeout(a, s, e, c) -> float:
            timeout = s.altitude * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__('land',
                         """
                (and (= $mode "LAND")
                    (> _altitude 0.3))
                         """,
                         """
                (and (= __mode "LAND")
                    (= _longitude __longitude)
                    (= _latitude __latitude)
                    (= __altitude 0.0)
                    (= __armed false))
                         """,
                         timeout)


class SetModeGuided(Specification):
    def __init__(self) -> None:
        super().__init__('guided',
                         """
                (= $mode "GUIDED")
                         """,
                         """
                (= __mode "GUIDED")
                         """)


class SetModeLoiter(Specification):
    def __init__(self) -> None:
        super().__init__('loiter',
                         """
                (= $mode "LOITER")
                         """,
                         """
                (= __mode "LOITER")
                         """)


class SetModeRTL(Specification):
    def __init__(self):
        def timeout(a, s, e, c):
            # compute distance
            from_loc = (s['latitude'], s['longitude'])
            to_loc = (s['home_latitude'], s['home_longitude'])
            dist = geopy.distance.great_circle(from_loc, to_loc).meters

            # compute time taken to travel from A to B, and time taken to land
            time_goto_phase = dist * c.time_per_metre_travelled
            time_land_phase = s['altitude'] * c.time_per_metre_travelled

            # compute total timeout
            timeout = \
                time_goto_phase + time_land_phase + s.constant_timeout_offset

            return timeout

        super().__init__('rtl',
                         """
                (= $mode "RTL")
                         """,
                         """
                (and (= __mode "RTL")
                    (ite (< _altitude 0.3) (= _armed __armed)
                        (= _armed false))
                    (= __longitude _home_longitude)
                    (= __latitude _home_latitude)
                    (= __altitude 0.0))
                         """,
                         timeout)


class SetMode(Command):
    name = 'set-mode'
    parameters = [
        Parameter('mode',
                  DiscreteValueRange(['GUIDED', 'LOITER', 'RTL', 'LAND']))
    ]
    specifications = [
        SetModeGuided(),
        SetModeLoiter(),
        SetModeRTL(),
        SetModeLand(),
        Idle
    ]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        sandbox.connection.mode = dronekit.VehicleMode(self.mode)
