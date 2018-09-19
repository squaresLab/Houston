__all__ = ['Takeoff']

import time
import math

from pymavlink import mavutil

from ...configuration import Configuration
from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...command import Parameter, Command
from ...specification import Specification, Idle
from ...valueRange import ContinuousValueRange


class TakeoffNormally(Specification):
    def __init__(self) -> None:
    	super().__init__("normal",
	    """
            (and (= _armed true)
                (= _mode "GUIDED")
                (< _altitude 0.3))
            """,
            """
            (and(= _longitude __longitude)
                (= _latitude __latitude)
                (= __altitude $altitude)
                (= __vz 0.0))
            """)
 

    def timeout(self, a, s, e, c) -> float:
        # FIXME add rate of ascent
        delta_alt = abs(a['altitude'] - s.altitude)
        t = delta_alt * c.time_per_metre_travelled
        t += c.constant_timeout_offset
        return t


class Takeoff(Command):
    name = 'takeoff'
    parameters = [
        Parameter('altitude', ContinuousValueRange(0.3, 100.0))
    ]
    specifications = [
        TakeoffNormally(),
        Idle()
    ]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 state: State,
                 environment: Environment,
                 config: Configuration
                 ) -> None:
        vehicle = sandbox.connection
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_NAV_TAKEOFF,
            0, 1, 0, 0, 0, 0, 0, self.altitude)
        vehicle.send_mavlink(msg)

