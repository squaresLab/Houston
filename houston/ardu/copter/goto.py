__all__ = ['GoTo']

import random
import dronekit
import geopy
from pymavlink.mavutil import mavlink

from ..connection import CommandLong
from ..common import GotoLoiter
from ...connection import Message
from ...specification import Specification
from ...configuration import Configuration
from ...command import Command, Parameter
from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...specification import Idle
from ...valueRange import ContinuousValueRange, DiscreteValueRange


def timeout_goto_normally(cmd: Command,
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


GotoNormally = Specification(
    'normal',
    """
    (and
        (= _armed true)
        (not (= _mode "LOITER"))
        (> _altitude 0.3))
    """,
    """
    (and
        (= __longitude $longitude)
        (= __latitude $latitude)
        (= __altitude $altitude))
    """,
    timeout_goto_normally)


class GoTo(Command):
    uid = 'ardu:copter:goto'
    name = 'goto'
    parameters = [
        Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True)),
        Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True)),
        Parameter('altitude', ContinuousValueRange(0.3, 100.0))
    ]
    specifications = [
        GotoNormally,
        GotoLoiter,
        Idle
    ]

    @classmethod
    def generate(cls, rng: random.Random) -> 'GoTo':
        (lat, lon) = (-35.3632607, 149.1652351)  # FIXME
        heading = rng.uniform(0.0, 360.0)
        dist = rng.uniform(0.0, 2.0)  # FIXME
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.distance(meters=dist)
        destination = dist.destination(origin, heading)
        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = 5.0  # FIXME

        command = cls(**params)
        return command

    def to_message(self) -> Message:
        return CommandLong(target_system=0,
                           target_component=0,
                           cmd_id=mavlink.MAV_CMD_NAV_WAYPOINT,
                           param_5=self.latitude,
                           param_6=self.longitude,
                           param_7=self.altitude)

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
