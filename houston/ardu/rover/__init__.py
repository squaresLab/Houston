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
        speedup = settings['speedup']
        return ArduRover(speedup=speedup)


    def __init__(self, speedup=3.0):
        assert isinstance(speedup, float)
        assert (speedup != 0.0)

        # variables specific to the ArduRover
        variables = []
        schemas = []

        super(ArduRover, self).__init__(variables, schemas, speedup=speedup)

    
    def setup(self, mission):
        super(ArduRover, self).setup(mission)


    # TODO: implement
    @property
    def repairbox_artefact(self):
        """
        Returns the RepairBox artefact used by this system.
        """
        from repairbox.manager import RepairBoxManager as rbx
        iden = 'ardubugs:copter:a0c5ac1'
        return rbx.bugs[iden]




System.register('ardurover', ArduRover)
