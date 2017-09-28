import time
import os
import sys
import math
import geopy
import geopy.distance

from houston.system import System
from houston.util import printflush
from houston.action import ActionSchema
from houston.state import   StateVariable, \
                            InternalVariable, \
                            ExternalVariable

# Attempt to import the modules necessary to interact with ArduPilot. If the
# necessary modules can't be imported, we report ArduPilot as uninstalled and
# prevent any interaction attempts.
try:
    import statistics # TODO where is this used?
    import dronekit
    import dronekit_sitl

    ARDUPILOT_INSTALLED = True
except ImportError as e:
    ARDUPILOT_INSTALLED = False


class BaseSystem(System):
    """
    Description of the ArduCopter system

    Attributes:
        __sitl (dronekit_sitl.SITL): a wrapper for the SITL simulator used to
            conduct the missions.
        __vehicle (dronekit.Vehicle): a connection to the vehicle under test,
            provided by dronekit.
        __speedup (float): speedup multiplier used by SITL.
    """
    def __init__(self, artefact_name, variables, schemas, speedup=3.0):
        """
        

        Args:
            speedup (float): speedup multiplied to use in SITL
            variables (list of Variable): TODO
            schemas (list of ActionSchema): TODO
        """
        assert isinstance(variables, list)
        assert all(isinstance(v, Variable) for v in variables)
        assert isinstance(schemas, list)
        assert all(isinstance(s, ActionSchema) for s in schemas)
        assert isinstance(speedup, float)
        assert (speedup != 0.0)

        self.__artefact_name = artefact_name
        self.__sitl = None
        self.__vehicle = None
        self.__speedup = speedup

        variables += [
            InternalVariable('homeLatitude', lambda: -35.362938), # TODO: fixed
            InternalVariable('homeLongitude', lambda: 149.165085), # TODO: fixed
            InternalVariable('altitude', lambda: self.__vehicle.location.global_relative_frame.alt, 1.0),
            InternalVariable('latitude', lambda: self.__vehicle.location.global_relative_frame.lat, 0.0005),
            InternalVariable('longitude', lambda: self.__vehicle.location.global_relative_frame.lon, 0.0005),
            InternalVariable('armable', lambda: self.__vehicle.is_armable),
            InternalVariable('armed', lambda: self.__vehicle.armed),
            InternalVariable('mode', lambda : self.__vehicle.mode.name),
            InternalVariable('vx', lambda: self.__vehicle.velocity[0]),
            InternalVariable('vy', lambda: self.__vehicle.velocity[1]),
            InternalVariable('vz', lambda: self.__vehicle.velocity[2])
        ]

        super(BaseSystem, self).__init__(variables, schemas)


    def to_json(self):
        """
        Returns a JSON-based description of this system.
        """
        jsn = super(BaseSystem, self).to_json()
        jsn['artefact'] = self.__artefact_name
        jsn['settings'] = {
            'speedup': self.__speedup
        }
        return jsn

    
    # TODO: internally, this should be a function of speedup
    @property
    def time_per_metre_travelled(self):
        return 1.0


    @property
    def constant_timeout_offset(self):
        """
        The constant offset that is added to all timeouts (the pinch of salt)
        """
        return 1.0


    @property
    def installed(self):
        return ARDUPILOT_INSTALLED

    
    @property
    def vehicle(self):
        """
        Uses dronekit to provide a connection to the system under test
        """
        return self.__vehicle


    @property
    def repairbox_artefact(self):
        from repairbox.manager import RepairBoxManager as rbx
        return rbx.bugs[self.__artefact_name]


    def setup(self, mission, binary_name, model_name, param_file):
        ardu_location = '/experiment/source/' # TODO: HARDCODED
        args = [
            "--model={}".format(model_name), # TODO: hardcoded
            "--home=-35.362938,149.165085,584,270", # TODO: HARDCODED
            "--speedup={}".format(self.__speedup)
        ]

        # TODO: HARDCODED
        param_file = '{}.parm'.format(param_file)
        param_file = os.path.join(ardu_location,
                                  'Tools/autotest/default_params',
                                  param_file)
        binary = os.path.join(ardu_location, 'build/sitl/bin', binary_name)
        self.__sitl = dronekit_sitl.SITL(binary, defaults_filepath=param_file) 
        self.__sitl.launch(args,
                           verbose=True,
                           await_ready=True,
                           restart=False,
                           wd='/experiment/') # TODO: HARDCODED

        connect_string = self.__sitl.connection_string()
        printflush(connect_string)
        self.__vehicle = dronekit.connect(connect_string, wait_ready=True)
        self.__vehicle.wait_ready('autopilot_version')

        # wait for longitude and latitude to match their expected values, and
        # for the system to match the expected `armable` state.
        initial_lon = mission.initial_state['longitude']
        initial_lat = mission.initial_state['latitude']
        while True:
            observed = self.observe()
            if self.variable('longitude').eq(initial_lon, observed['longitude']) and \
               self.variable('latitude').eq(initial_lat, observed['latitude']) and \
               observed['armable'] == mission.initial_state['armable']:
                break
            time.sleep(0.05)

        # wait until the vehicle is in GUIDED mode
        # TODO: add timeout
        guided_mode = dronekit.VehicleMode('GUIDED')
        self.vehicle.mode = guided_mode
        while self.vehicle.mode != guided_mode:
            time.sleep(0.05)


    def tear_down(self, mission):
        self.__vehicle.close()
        self.__vehicle = None
        self.__sitl.stop()
        self.__sitl = None
