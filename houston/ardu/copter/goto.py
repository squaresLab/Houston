__all__ = ['GoTo']

import dronekit
import geopy.distance

from ..common import GotoLoiter
from ...specification import Specification
from ...configuration import Configuration
from ...command import Command, Parameter
from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...specification import Idle
from ...valueRange import ContinuousValueRange, DiscreteValueRange


class GotoNormally(Specification):
    """
    If the robot is armed and not in its `LOITER` mode, GoTo actions should
    cause the robot to move to the desired location. For certain Ardu systems,
    the precondition on this normal behaviour is stronger; for more
    information, refer to the system-specific subclasses of GotoNormally.
    """

    def __init__(self) -> None:
        def timeout(cmd: Command,
                    s: State,
                    e: Environment,
                    c: Configuration
                    ) -> float:
            from_loc = (s['latitude'], s['longitude'])
            to_loc = (cmd['latitude'], cmd['longitude'])
            dist = geopy.distance.great_circle(from_loc, to_loc).meters
            timeout = dist * c.time_per_metre_travelled
            timeout += c.constant_timeout_offset
            return timeout

        super().__init__('normal',
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
                         timeout)


class GoTo(Command):
    name = 'goto'
    parameters = [
        Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
        Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
        Parameter('altitude', ContinuousValueRange(0.3, 100.0))
    ]
    specifications = [
        GotoNormally(),
        GotoLoiter(),
        Idle
    ]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        loc = dronekit.LocationGlobalRelative(self.latitude,
                                              self.longitude,
                                              self.altitude)
        sandbox.connection.simple_goto(loc)
