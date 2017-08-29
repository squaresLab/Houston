import sys
import time
import os
import sys
import subprocess as sub
import math
import geopy
import geopy.distance

import arm
import goto
import setmode
import takeoff

from houston.system import System
from houston.util import printflush
from houston.state import InternalVariable, ExternalVariable

# Attempt to import the modules necessary to interact with ArduPilot. If the
# necessary modules can't be imported, we report ArduPilot as uninstalled and
# prevent any interaction attempts.
try:
    import statistics # TODO where is this used?
    import dronekit
    import dronekit_sitl

    SAMPLE_BATTERY = []
    SAMPLE_TIME    = []
    WINDOW_BATTERY = .025
    WINDOW_TIME    = 2

    ARDUPILOT_INSTALLED = True
except ImportError as e:
    ARDUPILOT_INSTALLED = False
    print("Import warning: {}".format(e))


TIME_PER_METER_TRAVELED = 1.0
CONSTANT_TIMEOUT_OFFSET = 1.0


class ArduCopter(System):
    """
    Description of the ArduCopter system

    Attributes:
        __sitl (dronekit_sitl.SITL): a wrapper for the SITL simulator used to
            conduct the missions.
        __vehicle (dronekit.Vehicle): a connection to the vehicle under test,
            provided by dronekit.
        __speedup (float): speedup multiplier used by SITL.
    """
    @staticmethod
    def fromJSON(jsn):
        assert (isinstance(jsn, dict))
        assert ('settings' in jsn)
        settings = jsn['settings']
        speedup = settings['speedup']
        return ArduCopter(speedup=speedup)


    def __init__(self, speedup=3.0):
        assert (isinstance(speedup, float))
        assert (speedup != 0.0)

        self.__sitl = None
        self.__vehicle = None
        self.__speedup = speedup

        variables = [
            InternalVariable('homeLatitude', lambda: -35.362938), # TODO: fixed
            InternalVariable('homeLongitude', lambda: 149.165085), # TODO: fixed
            InternalVariable('altitude', lambda: self.__vehicle.location.global_relative_frame.alt, 1.0),
            InternalVariable('latitude', lambda: self.__vehicle.location.global_relative_frame.lat, 0.00002),
            InternalVariable('longitude', lambda: self.__vehicle.location.global_relative_frame.lon, 0.00002),
            InternalVariable('armable', lambda: self.__vehicle.is_armable),
            InternalVariable('armed', lambda: self.__vehicle.armed),
            InternalVariable('mode', lambda : self.__vehicle.mode.name),
        ]
        schemas = [
            goto.GoToSchema(),
            takeoff.TakeoffSchema(),
            arm.ArmSchema(),
            setmode.SetModeSchema()
        ]

        super(ArduCopter, self).__init__(variables, schemas)

    
    def toJSON(self):
        """
        Returns a JSON-based description of this system.
        """
        jsn = super(ArduCopter, self).toJSON()
        jsn['settings'] = {
            'speedup': self.__speedup
        }
        return jsn


    def installed(self):
        return ARDUPILOT_INSTALLED

    
    def getVehicle(self):
        """
        Uses dronekit to provide a connection to the system under test
        """
        return self.__vehicle


    def setUp(self, mission):
        ardu_location = '/experiment/source/' # TODO: HARDCODED
        args = [
            "--model=quad",
            "--home=-35.362938,149.165085,584,270", # TODO: HARDCODED
            "--speedup={}".format(self.__speedup)
        ]

        binary = os.path.join(ardu_location, 'build/sitl/bin/arducopter') # TODO: HARDCODED
        self.__sitl = dronekit_sitl.SITL(binary,
                                         defaults_filepath='/experiment/source/Tools/autotest/default_params/copter.parm') # TODO: HARDCODED
        self.__sitl.launch(args,
                           verbose=True,
                           await_ready=True,
                           restart=False,
                           wd='/experiment/') # TODO: HARDCODED

        connectString = self.__sitl.connection_string()
        printflush(connectString)
        self.__vehicle = dronekit.connect(connectString, wait_ready=True)
        self.__vehicle.wait_ready('autopilot_version')

        vehicleMode = dronekit.VehicleMode('GUIDED')
        self.__vehicle.mode = vehicleMode
        self.__vehicle.parameters['DISARM_DELAY'] = 0
        self.__vehicle.parameters['RTL_ALT'] = 0

        while self.__vehicle.parameters['DISARM_DELAY'] != 0 and not self.__vehicle.is_armable: #TODO Implement timeout
            time.sleep(0.1)
            self.__vehicle.mode = vehicleMode
            self.__vehicle.parameters['DISARM_DELAY'] = 0
            self.__vehicle.parameters['RTL_ALT'] = 0


    def tearDown(self, mission):
        self.__vehicle.close()
        self.__vehicle = None
        self.__sitl.stop()
        self.__sitl = None


# Register the ArduCopter system type
System.register('arducopter', ArduCopter)
