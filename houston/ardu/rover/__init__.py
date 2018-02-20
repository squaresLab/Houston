import time
import bugzoo
from houston.ardu.rover.sandbox import Sandbox
from houston.util import printflush
from houston.ardu.base import BaseSystem


class ArduRover(BaseSystem):
    def __init__(self,
                 snapshot: bugzoo.Bug,
                 speedup=3.0):
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.rover.goto import GoToSchema

        # TODO: RTL_ALT: http://ardupilot.org/copter/docs/rtl-mode.html
        # rover-specific system variables
        variables = []
        schemas = [
            GoToSchema(),
            ArmDisarmSchema()
        ]

        super(ArduRover, self).__init__(snapshot,
                                        variables,
                                        schemas,
                                        speedup=speedup)

    def provision(self) -> Sandbox:
        return Sandbox(self)
