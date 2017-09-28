import time
from houston.util import printflush
from houston.ardu.base import BaseSystem
from houston.system import System


class ArduRover(BaseSystem):
    """
    Description of the ArduRover system
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)
        assert ('settings' in jsn)
        settings = jsn['settings']
        speedup = settings.get('speedup', 3.0)
        artefact = jsn['artefact']
        return ArduRover(artefact, speedup=speedup)


    def __init__(self, artefact, speedup=3.0):
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.rover.goto import GoToSchema

        # TODO: RTL_ALT: http://ardupilot.org/copter/docs/rtl-mode.html
        # rover-specific system variables
        variables = []
        schemas = [
            GoToSchema(),
            ArmDisarmSchema()
        ]

        super(ArduRover, self).__init__(artefact, variables, schemas, speedup=speedup)


    def setup(self, mission):
        super(ArduRover, self).setup(mission,   binary_name='ardurover',
                                                model_name='rover',
                                                param_file='rover')

   
System.register('ardurover', ArduRover)
