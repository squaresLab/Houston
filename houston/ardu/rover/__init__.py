import time

# TODO: import schemas

from houston.util import printflush
from houston.ardu.base import BaseSystem
from houston.system import System

try:
    import dronekit
except ImportError:
    pass


class ArduRover(BaseSystem):
    """
    Description of the ArduRover system
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)
        assert ('settings' in jsn)
        settings = jsn['settings']
        speedup = settings['speedup']
        return ArduRover(speedup=speedup)


    def __init__(self, speedup=3.0):
        assert (isinstance(speedup, float))
        assert (speedup != 0.0)

        # variables specific to the ArduRover
        variables = []
        schemas = []

        super(ArduRover, self).__init__(variables, schemas, speedup=speedup)

    
    def setup(self, mission):
        super(ArduRover, self).setup(mission)
        
        # TODO


System.register('ardurover', ArduRover)
