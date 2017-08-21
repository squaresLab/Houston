# These should be conditional imports
import sys
import time
import os
import sys
import subprocess as sub

import houston

from valueRange import DiscreteValueRange, ContinuousValueRange
from system     import System, ActionSchema, Branch
from action     import ActionSchema, Action, Parameter, ActionGenerator
from predicate  import Invariant, Postcondition, Precondition
from state      import Estimator, FixedEstimator
from state      import InternalVariable, ExternalVariable
from branch     import Branch, IdleBranch

import geopy
import geopy.distance

# Attempt to import the modules necessary to interact with ArduPilot. If the
# necessary modules can't be imported, we report ArduPilot as uninstalled and
# prevent any interaction attempts.
try:
    # TODO always prefer "import" over "from"
    import pexpect
    import statistics
    from pymavlink      import mavutil, mavwp
    from dronekit_sitl  import SITL
    from dronekit       import connect, VehicleMode, LocationGlobalRelative

    testdir = os.path.abspath("/experiment/source/Tools/autotest")
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
    print("Import warning: {}".format(e))


DRONEKIT_SYSTEM = None
TIME_PER_METER_TRAVELED = 1.0
CONSTANT_TIMEOUT_OFFSET = 1.0

class ArduPilot(System):
    """
    Description of the ArduPilot system
    """

    def __init__(self):
        self.__sitl       = None
        self.__mavproxy   = None
        self.__mavlink    = None

        variables = {}
        # TODO: this is very tricky; we'll need to do something clever here
        variables['homeLatitude'] = \
            InternalVariable('homeLatitude', lambda: -35.362938) # Fixed
        variables['homeLongitude'] = \
            InternalVariable('homeLongitude', lambda: 149.165085) # Fixed
        variables['altitude'] = \
            InternalVariable('altitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.alt, 0.3)
        variables['latitude'] = \
            InternalVariable('latitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.lat, 0.00001)
        variables['longitude'] = \
            InternalVariable('longitude', lambda: DRONEKIT_SYSTEM.location.global_relative_frame.lon, 0.00001)
        variables['armable'] = \
            InternalVariable('armable', lambda: DRONEKIT_SYSTEM.is_armable)
        variables['armed'] = \
            InternalVariable('armed', lambda: DRONEKIT_SYSTEM.armed)
        variables['mode'] = \
            InternalVariable('mode', lambda : DRONEKIT_SYSTEM.mode.name)

        schemas = {
            'goto'   : GoToActionSchema(),
            'takeoff': TakeoffActionSchema(),
            'arm'    : ArmActionSchema(),
            'setmode'   : SetModeActionSchema()
        }

        super(ArduPilot, self).__init__('ardupilot', variables, schemas)


    def installed(self):
        return ARDUPILOT_INSTALLED


    def setUp(self, mission):
    	global DRONEKIT_SYSTEM
        global DRONEKIT_SITL
        ardu_location = '/experiment/source/'

        args = [
            "--model=quad",
            "--home=-35.362938,149.165085,584,270",
            "--speedup=5"
        ]

        binary = os.path.join(ardu_location, 'build/sitl/bin/arducopter')
        DRONEKIT_SITL = SITL(binary, defaults_filepath='/experiment/source/Tools/autotest/default_params/copter.parm')
        DRONEKIT_SITL.launch(args, verbose=True, await_ready=True, restart=False,  wd='/experiment/')
        connectString = DRONEKIT_SITL.connection_string()
        print connectString
        sys.stdout.flush()
        DRONEKIT_SYSTEM = connect(connectString, wait_ready=True)
        DRONEKIT_SYSTEM.wait_ready('autopilot_version')
        vehicleMode = VehicleMode('GUIDED')
        DRONEKIT_SYSTEM.mode = vehicleMode
        DRONEKIT_SYSTEM.parameters['DISARM_DELAY']=0
        while DRONEKIT_SYSTEM.parameters['DISARM_DELAY'] is not 0 and DRONEKIT_SYSTEM.is_armable is False: #TODO Implement timeout
            time.sleep(0.1)
            DRONEKIT_SYSTEM.mode = vehicleMode
            DRONEKIT_SYSTEM.parameters['DISARM_DELAY']=0


    def setUpOld(self, mission):
    	global DRONEKIT_SYSTEM
        # TODO lots of hardcoded paths
        ardu_location = '/experiment/source/' # TODO: hardcoded!
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
        DRONEKIT_SITL.stop()

    def tearDownOld(self, mission):
        DRONEKIT_SYSTEM.close()
        util.pexpect_close(self.__mavproxy)
        util.pexpect_close(self.__mavlink)


class ArmActionSchema(ActionSchema):
    """docstring for ArmActionSchema."""
    def __init__(self):
        parameters = []
        branches = [
            ArmNormalBranch(self),
            IdleBranch(self)
        ]
        super(ArmActionSchema, self).__init__('arm', parameters, branches)


    def dispatch(self, action, state, environment):
        DRONEKIT_SYSTEM.armed = True
        while not DRONEKIT_SYSTEM.armed:
            time.sleep(0.1)


class ArmNormalBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('armed', True)
        ]
        super(ArmNormalBranch, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def isApplicable(self, action, state, environment):
        return state.read('armable') and (state.read('mode') == 'GUIDED' or state.read('mode') == 'LOITER')


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)


    def generate(self, state, environment):
        return self.getSchema.generate()


class SetModeActionSchema(ActionSchema):
    """docstring for SetModeActionSchema"""
    def __init__(self):
        parameters = [
            Parameter('mode', DiscreteValueRange(['GUIDED', 'LOITER', 'RTL', 'LAND']),\
                      'description')
        ]
        branches = [
            SetModeGuidedBranch(self),
            SetModeLoiterBranch(self),
            SetModeRTLBranch(self),
            SetModeLandBranch(self),
            IdleBranch(self)
        ]

        super(SetModeActionSchema, self).__init__('setmode', parameters, branches)

    def dispatch(self, action, state, environment):
        vehicleMode = VehicleMode(action.read('mode'))
        DRONEKIT_SYSTEM.mode = vehicleMode

        if action.read('mode') == 'RTL':
            currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt
            currentLat  = DRONEKIT_SYSTEM.location.global_relative_frame.lat
            currentLon = DRONEKIT_SYSTEM.location.global_relative_frame.lon
            toLocation = (state.read('homeLatitude'), state.read('homeLongitude'))
            fromLocation = (currentLat, currentLon)

            while not DRONEKIT_SYSTEM.mode == vehicleMode:
                time.sleep(0.2)

            while geopy.distance.great_circle(fromLocation, toLocation).meters > 0.3 and \
                currentAlt > 0.1:
                time.sleep(0.2)
                currentLat = DRONEKIT_SYSTEM.location.global_relative_frame.lat
                currentLon = DRONEKIT_SYSTEM.location.global_relative_frame.lon
                currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt

        elif action.read('mode') == 'LAND':
            currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt

            while not DRONEKIT_SYSTEM.mode == vehicleMode:
                time.sleep(0.2)

            while currentAlt > 0.1:
                time.sleep(0.2)
                currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt
        else: # TODO as we add more modes this would have to change
            while not DRONEKIT_SYSTEM.mode == vehicleMode:
                time.sleep(0.1)


class SetModeLandBranch(Branch):
    """
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'LAND'),
            FixedEstimator('armed', False),
            Estimator('latitude', lambda action, state, env: state.read('latitude')),
            Estimator('longitude', lambda action, state, env: state.read('longitude')),
            Estimator('altitude', lambda action, state, env: 0.0)
        ]
        super(SetModeLandBranch, self).__init__('land', schema, estimators)


    def computeTimeout(self, action, state, environment):
        timeout = (state.read('altitude') * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def isApplicable(self, action, state, environment):
        return action.read('mode') == 'LAND'


    def isSatisfiable(self, state, environment):
        return True


    def generate(self, state, environment):
        return Action(self.getSchemaName(), {'mode': 'LAND'})


class SetModeGuidedBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'GUIDED')
        ]
        super(SetModeGuidedBranch, self).__init__('guided', schema, estimators)


    def computeTimeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def isApplicable(self, action, state, environment):
        return action.read('mode') == 'GUIDED'


    def isSatisfiable(self, state, environment):
        return True


    def generate(self, state, environment):
        return Action(self.getSchemaName(), {'mode': 'GUIDED'})



class SetModeLoiterBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'LOITER')
        ]
        super(SetModeLoiterBranch, self).__init__('loiter', schema, estimators)


    def computeTimeout(self, action, state, environment):
        return CONSTANT_TIMEOUT_OFFSET


    def isApplicable(self, action, state, environment):
        return action.read('mode') == 'LOITER'


    def isSatisfiable(self, state, environment):
        return True


    def generate(self, state, environment):
        return Action(self.getSchemaName(), {'mode': 'LOITER'})


class SetModeRTLBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            FixedEstimator('mode', 'RTL'),
            Estimator('latitude', lambda action, state, env: state.read('homeLatitude')),
            Estimator('longitude', lambda action, state, env: state.read('homeLongitude')),
            Estimator('altitude', lambda action, state, env: 0.0)
        ]
        super(SetModeRTLBranch, self).__init__('rtl', schema, estimators)


    def computeTimeout(self, action, state, environment):
        fromLocation = (state.read('latitude'), state.read('longitude'))
        toLocation   = (state.read('homeLatitude'), state.read('homeLongitude'))
        totalDistance = geopy.distance.great_circle(fromLocation, toLocation).meters
        landTime = state.read('altitude') * TIME_PER_METER_TRAVELED
        timeout = (totalDistance * TIME_PER_METER_TRAVELED) + CONSTANT_TIMEOUT_OFFSET + landTime
        return timeout


    def isApplicable(self, action, state, environment):
        return action.read('mode') == 'RTL'


    def isSatisfiable(self, state, environment):
        return True


    def generate(self, state, environment):
        return Action(self.getSchemaName(), {'mode': 'RTL'})


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
            GotoNormalBranch(self),
            IdleBranch(self)
        ]

        super(GoToActionSchema, self).__init__('goto', parameters, branches)


    def dispatch(self, action, state, environment):
        DRONEKIT_SYSTEM.simple_goto(LocationGlobalRelative(
            action.read('latitude'),
            action.read('longitude'),
            action.read('altitude'))
        )
        currentLat  = DRONEKIT_SYSTEM.location.global_relative_frame.lat
        currentLon = DRONEKIT_SYSTEM.location.global_relative_frame.lon
        toLocation = (action.getValue('latitude'), action.getValue('longitude'))
        fromLocation = (currentLat, currentLon)

        while geopy.distance.great_circle(fromLocation, toLocation).meters > 0.3:
            time.sleep(.2)
            currentLat  = DRONEKIT_SYSTEM.location.global_relative_frame.lat
            currentLon = DRONEKIT_SYSTEM.location.global_relative_frame.lon


class GotoNormalBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('latitude', lambda action, state, env: action.read('latitude')),
            Estimator('longitude', lambda action, state, env: action.read('longitude')),
            Estimator('altitude', lambda action, state, env: action.read('altitude'))
        ]
        super(GotoNormalBranch, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        fromLocation = (state.read('latitude'), state.read('longitude'))
        toLocation   = (action.getValue('latitude'), action.getValue('longitude'))
        totalDistance = geopy.distance.great_circle(fromLocation, toLocation).meters
        timeout = totalDistance * TIME_PER_METER_TRAVELED + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def isApplicable(self, action, state, environment):
        return state.read('armed') and state.read('altitude') > 0.3


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)


    def generate(self, state, environment):
        return self.getSchema().generate()


class DistanceBasedGoToGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, maxDistance, minDistance = 1.0):
        assert (isinstance(maxDistance, float) and maxDistance is not None)
        assert (isinstance(minDistance, float) and minDistance is not None)
        assert (maxDistance > minDistance)
        assert (minDistance > 0.0)

        self.__maxDistance = maxDistance
        parameters = [
            Parameter('distance', ContinuousValueRange(minDistance, maxDistance)),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True))
        ]

        super(DistanceBasedGoToGenerator, self).__init__('goto', parameters)


    def constructWithState(self, currentState, env, values):
        dist = values['distance']
        heading = values['heading']
        lon = currentState.read('longitude')
        lat = currentState.read('latitude')
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination =  dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = currentState.read('altitude')

        return params


    def constructWithoutState(self, env, values):
        raise NotImplementedError


class CircleBasedGotoGenerator(ActionGenerator):
    """
    Description.
    """

    def __init__(self, centerCoordinates, radius):
        assert (isinstance(centerCoordinates, tuple) and centerCoordinates is not None)
        assert (isinstance(radius, float) and radius is not None)
        self.__centerCoordinates = centerCoordinates
        self.__radius = radius

        parameters = [
            Parameter('latitude', DiscreteValueRange([centerCoordinates[0]])),
            Parameter('longitude', DiscreteValueRange([centerCoordinates[1]])),
            Parameter('heading', ContinuousValueRange(0.0, 360.0, True)),
            Parameter('distance', ContinuousValueRange(0.0, radius))
        ]
        super(CircleBasedGotoGenerator, self).__init__('goto', parameters)


    def constructWithoutState(self, env, values):
        lat = values['latitude']
        lon = values['longitude']
        heading = values['heading']
        dist = values['distance']
        params = {}

        origin = geopy.Point(latitude=lat, longitude=lon)
        dist = geopy.distance.VincentyDistance(meters=dist)
        destination =  dist.destination(origin, heading)

        params['latitude'] = destination.latitude
        params['longitude'] = destination.longitude
        params['altitude'] = 10.0 # small limitation since we don't have current
                                  # state to get altitude.

        return params


    def constructWithState(self, currentState, env, values):
        return self.constructWithoutState(env, values)



class TakeoffActionSchema(ActionSchema):
    """docstring for TakeoffActionSchema."""
    def __init__(self):
        parameters = [
            Parameter('altitude', ContinuousValueRange(0.3, 100.0),\
                      'description')
        ]
        branches = [
            TakeoffNormalBranch(self),
            IdleBranch(self)
        ]

        super(TakeoffActionSchema, self).__init__('takeoff', parameters, branches)


    def dispatch(self, action, state, environment):
        DRONEKIT_SYSTEM.simple_takeoff(action.getValue('altitude'))

        expectedAlt = action.read('altitude')
        currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt

        while currentAlt < expectedAlt - 0.3: # OFFSET
            time.sleep(.1)
            currentAlt = DRONEKIT_SYSTEM.location.global_relative_frame.alt


class TakeoffNormalBranch(Branch):
    """
    Description.
    """
    def __init__(self, schema):
        estimators = [
            Estimator('altitude', lambda action, state, env: action.read('altitude'))
        ]
        super(TakeoffNormalBranch, self).__init__('normal', schema, estimators)


    def computeTimeout(self, action, state, environment):
        timeout = action.read('altitude') * TIME_PER_METER_TRAVELED + CONSTANT_TIMEOUT_OFFSET
        return timeout


    def isApplicable(self, action, state, environment):
        return state.read('armed') and state.read('altitude') < 0.3 and state.read('mode') == 'GUIDED' #TODO further check


    def isSatisfiable(self, state, environment):
        return self.isApplicable(None, state, environment)


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
