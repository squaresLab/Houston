# These should be conditional imports
import sys
import time
import os
import sys
import subprocess as sub

import houston
from valueRange import DiscreteValueRange, ContinuousValueRange
from system     import System, ActionSchema
from mission    import Parameter
from predicate  import Invariant, Postcondition, Precondition
from state      import Estimator
from state      import InternalVariable, ExternalVariable
# Attempt to import the modules necessary to interact with ArduPilot. If the
# necessary modules can't be imported, we report ArduPilot as uninstalled and
# prevent any interaction attempts.
try:
    # TODO always prefer "import" over "from"
    import pexpect
    import statistics
    from pymavlink      import mavutil, mavwp
    from geopy          import distance
    from dronekit_sitl  import SITL
    from dronekit       import connect, VehicleMode, LocationGlobalRelative

    testdir = os.path.abspath("/home/robot/ardupilot/Tools/autotest")
    sys.path.append(testdir)

    from common import expect_callback, expect_list_clear, expect_list_extend, message_hook, idle_hook
    from pysim import util, vehicleinfo

    SAMPLE_BATTERY = []
    SAMPLE_TIME    = []
    WINDOW_BATTERY = .025
    WINDOW_TIME    = 2

    vinfo = vehicleinfo.VehicleInfo()

    ARDUPILOT_INSTALLED = True
except ImportError as e:
    ARDUPILOT_INSTALLED = False

DRONEKIT_SYSTEM = None

"""
Description of the ArduPilot system
"""
class ArduPilot(System):

    def __init__(self):
        self.__sitl       = None
        self.__mavproxy   = None
        self.__mavlink    = None

        variables = {}
        # TODO: this is very tricky; we'll need to do something clever here
        variables['time'] = \
            InternalVariable('time', lambda: time.time())
        variables['homeLatitude'] = \
            InternalVariable('homeLatitude', lambda: 149.165085) # Fixed
        variables['homeLongitude'] = \
            InternalVariable('homeLongitude', lambda: -35.362938) # Fixed
        variables['altitude'] = \
            InternalVariable('altitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.alt)
        variables['latitude'] = \
            InternalVariable('latitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.lat)
        variables['longitude'] = \
            InternalVariable('longitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.lon)
        variables['battery'] = \
            InternalVariable('battery', lambda: DRONEKIT_SYSTEM.battery.level)
        variables['armable'] = \
            InternalVariable('armable', lambda: DRONEKIT_SYSTEM.is_armable)
        variables['armed'] = \
            InternalVariable('armed', lambda: DRONEKIT_SYSTEM.armed)
        variables['mode'] = \
            InternalVariable('mode', lambda : DRONEKIT_SYSTEM.mode.name)

        schemas = {
            'goto'   : GoToActionSchema(),
            'takeoff': TakeoffActionSchema(),
            'land'   : LandActionSchema(),
            'arm'    : ArmActionSchema(),
            'setmode'   : SetModeActionSchema()
        }

        super(ArduPilot, self).__init__('ardupilot', variables, schemas)


    def installed(self):
        return ARDUPILOT_INSTALLED


    def systemAlive(self):
        return True #TODO


    def setUp(self, mission):
    	global DRONEKIT_SYSTEM
        # TODO lots of hardcoded paths
        ardu_location = '/home/robot/ardupilot' # TODO: hardcoded!
        binary = os.path.join(ardu_location, 'build/sitl/bin/arducopter')
        param_file = os.path.join(ardu_location, 'Tools/autotest/default_params/copter.parm')

        sitl = util.start_SITL(binary, wipe=True, model='quad', home='-35.362938, 149.165085, 584, 270', speedup=5)
        mavproxy = util.start_MAVProxy_SITL('ArduCopter', options='--sitl=127.0.0.1:5501 --out=127.0.0.1:19550 --quadcopter')
        mavproxy.expect('Received [0-9]+ parameters')

        # setup test parameters
        params = vinfo.options["ArduCopter"]["frames"]['quad']["default_params_filename"]
        if not isinstance(params, list):
            params = [params]
            for x in params:
                mavproxy.send("param load %s\n" % os.path.join(testdir, x))

        mavproxy.expect('Loaded [0-9]+ parameters')
        mavproxy.send("param set LOG_REPLAY 1\n")
        mavproxy.send("param set LOG_DISARMED 1\n")
        time.sleep(2)

        # reboot with new parameters
        util.pexpect_close(mavproxy)
        util.pexpect_close(sitl)

        self.__sitl  = util.start_SITL(binary, model='quad', home='-35.362938, 149.165085, 584, 270', speedup=5, valgrind=False, gdb=False)
        options = '--sitl=127.0.0.1:5501 --out=127.0.0.1:19550 --out=127.0.0.1:14550 --quadcopter --streamrate=5'
        self.__mavproxy = util.start_MAVProxy_SITL('ArduCopter', options=options)
        self.__mavproxy.expect('Telemetry log: (\S+)')
        logfile = self.__mavproxy.match.group(1)
        print("LOGFILE %s" % logfile)

        # the received parameters can come before or after the ready to fly message
        self.__mavproxy.expect(['Received [0-9]+ parameters', 'Ready to FLY'])
        self.__mavproxy.expect(['Received [0-9]+ parameters', 'Ready to FLY'])

        util.expect_setup_callback(self.__mavproxy, expect_callback)

        expect_list_clear()
        expect_list_extend([sitl, self.__mavproxy])
        # get a mavlink connection going
        try:
            self.__mavlink = mavutil.mavlink_connection('127.0.0.1:19550', robust_parsing=True)
        except Exception as msg:
            print("Failed to start mavlink connection on 127.0.0.1:19550 {}".format(msg))
            raise
        self.__mavlink.message_hooks.append(message_hook)
        self.__mavlink.idle_hooks.append(idle_hook)

        try:
            self.__mavlink.wait_heartbeat()
            """Setup RC override control."""
            for chan in range(1, 9):
                self.__mavproxy.send('rc %u 1500\n' % chan)
            # zero throttle
            self.__mavproxy.send('rc 3 1000\n')
            self.__mavproxy.expect('IMU0 is using GPS')
            DRONEKIT_SYSTEM = connect('127.0.0.1:14550', wait_ready=True)
        except pexpect.TIMEOUT:
            print("Failed: time out")
            return False

    def tearDown(self, mission):
        DRONEKIT_SYSTEM.close()
        util.pexpect_close(self.__mavproxy)
        util.pexpect_close(self.__mavlink)


class ArmActionSchema(ActionSchema):
    """docstring for ArmActionSchema."""
    def __init__(self):
        parameters = []
        branches = [
            OutcomeBranch(lambda action, state, env: state.read('armable') and state.read('mode') == 'GUIDED', [
                FixedEstimator('armed', True)])
        ]
        super(ArmActionSchema, self).__init__('arm', parameters, branches)

    def dispatch(self, action):
        DRONEKIT_SYSTEM.armed = True

    def computeTimeout(self, action, state, environment):
        pass


class SetModeActionSchema(ActionSchema):
    """docstring for SetModeActionSchema"""
    def __init__(self):
        parameters = [
            Parameter('mode', DiscreteValueRange(['GUIDED', 'LOITER', 'RTL']),\
                      'description')
        ]
        branches = [
            OutcomeBranch(lambda action, state, env: action.read('mode') == 'RTL', [
                FixedEstimator('mode', 'RTL'),
                FixedEstimator('armed', False),
                FixedEstimator('altitude', 0.0),
                # BATTERY
                Estimator('latitude', lambda action, state, env: state.read('homeLatitude')),
                Estimator('longitude', lambda action, state, env: state.read('homeLongitude'))
            ]),
            OutcomeElseBranch([
                Estimator('mode', lambda action, state, env: action.read('mode'))])
        ]

        super(SetModeActionSchema, self).__init__('setmode', parameters, branches)

    def dispatch(self, action):
        DRONEKIT_SYSTEM.mode = VehicleMode(action.getValue('mode'))

    def computeTimeout(self, action, state, environment):
        pass


class GoToActionSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('latitude', ContinuousValueRange(-90.0, 90.0, True),\
                      'description'),
            Parameter('longitude', ContinuousValueRange(-180.0, 180.0, True),\
                      'description'),
            Parameter('altitude', ContinuousValueRange(0.3, 100.0),\
                      'description')
        ]

        branches = [
            OutcomeBranch(lambda action, state, env:
                state.read('armed') and state.read('altitude') > 0.3, [
                Estimator('latitude', lambda action, state, env: action.read('latitude')),
                Estimator('longitude', lambda action, state, env: action.read('longitude')),
                Estimator('altitude', lambda action, state, env: action.read('altitude'))
            ])

        super(GoToActionSchema, self).__init__('goto',parameters, preconditions,\
            invariants, postconditions, estimators)


    def dispatch(self, action):
        DRONEKIT_SYSTEM.simple_goto(LocationGlobalRelative(
            action.getValue('latitude'),
            action.getValue('longitude'),
            action.getValue('altitude')
        ))

    def computeTimeout(self, action, state, environment):
        fromLocation = (state.read('latitude'), state.read('longitude'))
        toLocation   = (action.getValue('latitude', 'longitude'))
        totalDistance = distance.great_circle(fromLocation, toLocation).meters
        return totalDistance * TIME_PER_METER_TRAVELED + CONSTANT_TIMEOUT_OFFSET


class LandActionSchema(ActionSchema):
    def __init__(self):
        parameters = []
        branches = [
            OutcomeBranch(lambda action, state, env:
                state.read('armed') and state.read('altitude') > 0.3, [
                FixedEstimator('altitude', 0.0) # TODO Not entirely true
                FixedEstimator('mode', 'LAND')
            ])
        ]

        super(LandActionSchema, self).__init__('land', parameters, preconditions,\
            invariants, postconditions, estimators)


    def dispatch(self, action):
        DRONEKIT_SYSTEM.mode = VehicleMode('LAND')

    def computeTimeout(self, action, state, environment):
        pass


class TakeoffActionSchema(ActionSchema):
    """docstring for TakeoffActionSchema."""
    def __init__(self):
        parameters = [
            Parameter('altitude', ContinuousValueRange(0.3, 100.0),\
                      'description')
        ]
        branches = [
            OutcomeBranch(lambda action, state, env:
                state.read('armed') and state.read('altitude') < 0.3,
                Estimator('altitude', lambda action, state, env: action.read('altitude')))
        ]

        super(TakeoffActionSchema, self).__init__('takeoff', parameters, \
            preconditions, invariants, postconditions, estimators)


    def dispatch(self, action):
        DRONEKIT_SYSTEM.simple_takeoff(action.getValue('altitude'))

    def computeTimeout(self, action, state, environment):
        pass


def maxExpectedBatteryUsage(latitude, longitude, altitude):
    return 0.01
    distance = distance.great_circle((0['latitude'], \
        system_variables['longitude']), (prime_latitude, prime_longitude))
    standard_dev, mean  = getStandardDeaviationAndMean(SAMPLE_BATTERY)
    #return (mean + standard_dev + WINDOW_BATTERY) * distance


def maxExpectedTime(prime_latitude, prime_longitude, prime_altitude):
    return 10
    distance = distance.great_circle((system_variables['latitude'], \
        system_variables['longitude']), (prime_latitude, prime_longitude))
    standard_dev, mean  = getStandardDeaviationAndMean(SAMPLE_TIME)
    #return (mean + standard_dev + WINDOW_BATTERY) * distance



def getStandardDeaviationAndMean(sample):
    return statistics.stdev(sample), numpy.mean(sample)


# Register the ArduPilot system
houston.registerSystem(ArduPilot())
