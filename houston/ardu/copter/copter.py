import time
from houston.util import printflush
from houston.ardu.base import BaseSystem
from houston.system import System


class ArduCopter(BaseSystem):
    """
    Description of the ArduCopter system
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)
        assert ('settings' in jsn)
        settings = jsn['settings']
        speedup = settings['speedup']
        return ArduCopter(speedup=speedup)


    def __init__(self, speedup=3.0):
        from houston.ardu.common import ArmSchema
        from houston.ardu.copter.goto import GoToSchema
        from houston.ardu.copter.setmode import SetModeSchema
        from houston.ardu.copter.takeoff import TakeoffSchema

        assert isinstance(speedup, float)
        assert (speedup != 0.0)

        # variables specific to the ArduCopter system
        variables = []
        schemas = [
            GoToSchema(),
            TakeoffSchema(),
            ArmSchema(),
            SetModeSchema()
        ]

        super(ArduCopter, self).__init__(variables, schemas, speedup=speedup)


    def setup(self, mission):
        super(ArduCopter, self).setup(mission,  binary_name='arducopter',
                                                model_name='quad',
                                                param_file='copter')

    
# Register the ArduCopter system type
System.register('arducopter', ArduCopter)
