import time
from houston.ardu.rover.sandbox import Sandbox
from houston.util import printflush
from houston.ardu.base import BaseSystem


class ArduRover(BaseSystem):
    def __init__(self,
                 bug_name: str,
                 speedup=3.0):
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.rover.goto import GoToSchema

        # TODO: RTL_ALT: http://ardupilot.org/copter/docs/rtl-mode.html
        # rover-specific system variables
        schemas = [
            GoToSchema(),
            ArmDisarmSchema()
        ]

        super(ArduRover, self).__init__(bug_name,
                                        schemas,
                                        speedup=speedup)

    def provision(self) -> Sandbox:
        return Sandbox(self)
