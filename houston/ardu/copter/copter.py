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
        assert ('artefact' in jsn)
        settings = jsn['settings']
        artefact_name = jsn['artefact']
        speedup = settings.get('speedup', 3.0)
        return ArduCopter(artefact_name, speedup=speedup)


    def __init__(self, artefact_name, speedup=3.0, min_parachute_alt=10.0):
        from houston.ardu.common import ArmDisarmSchema
        from houston.ardu.copter.goto import GoToSchema
        from houston.ardu.copter.setmode import SetModeSchema
        from houston.ardu.copter.takeoff import TakeoffSchema
        from houston.ardu.copter.parachute import ParachuteSchema

        assert isinstance(speedup, float)
        assert (speedup != 0.0)

        self.__min_parachute_alt = min_parachute_alt

        # variables specific to the ArduCopter system
        variables = []
        schemas = [
            GoToSchema(),
            TakeoffSchema(),
            ArmDisarmSchema(),
            SetModeSchema(),
            ParachuteSchema()
        ]

        super(ArduCopter, self).__init__(artefact_name, variables, schemas, speedup=speedup)


    @property
    def min_parachute_alt(self):
        return self.__min_parachute_alt


    def setup(self, mission):
        super(ArduCopter, self).setup(mission,  binary_name='arducopter',
                                                model_name='quad',
                                                param_file='copter')

        # TODO: is part of this common?
        self.vehicle.parameters['DISARM_DELAY'] = 0
        self.vehicle.parameters['RTL_ALT'] = 0

        # wait until copter is in desired configuration
        while True:
            if self.vehicle.parameters['DISARM_DELAY'] == 0 and \
               self.vehicle.parameters['RTL_ALT'] == 0:
                break
            time.sleep(0.05)


    
# Register the ArduCopter system type
System.register('arducopter', ArduCopter)
