import rospy
import numpy
import statistics
import time
from geopy             import distance
from nav_msgs.msg      import Odometry
from mavros_msgs.msg   import BatteryStatus, State
from sensor_msgs.msg   import NavSatFix


SAMPLE_BATTERY = []
SAMPLE_TIME    = []
WINDOW_BATTERY = .025
WINDOW_TIME    = 2

system_variables = {}
system_variables['time'] = \
    lambda: time.time()
system_variables['altitude'] = \
    lambda: rospy.client.wait_for_message('/mavros/local_position/odom',
                                           Odometry,
                                           timeout=1.0).pose.pose.position.z
system_variables['latitude'] = \
    lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                                           NavSatFix,
                                           timeout=1.0).latitude
system_variables['longitude'] = \
    lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                                          NavSatFix,
                                          timeout=1.0).longitude
system_variables['battery'] = \
    lambda: rospy.client.wait_for_message('/mavros/battery',
                                          BatteryStatus,
                                          timeout=1.0).remaining
system_variables['arm'] = \
    lambda : rospy.client.wait_for_message('/mavros/state',
                                           State,
                                           timeout=1.0).armed
system_variables['mode'] = \
    lambda : rospy.client.wait_for_message('/mavros/state',
                                           State,
                                           timeout=1.0).mode

action['goto'] = Action(
    # Description
    'Commands the system to go to a specific location.',
    # Parameters
    [
        Parameter('latitude', float, 'description'),
        Parameter('longitude', float, 'description'),
        Parameter('altitude', float, 'description')
    ],
    # Preconditions
    [
        # get sv from parameters, I think there's no need for lambdas here
        Precondition('battery', lambda sv: system_variables['battery'] >= max_expected_battery_usage\
        (sv['latitude'], sv['longitude'], sv['altitude']), 'description')
        Precondition('altitude', lambda : system_variables['altitude'] > 0, 'description')
    ],
    # Invariants
    [
        Invariants('battery', lambda : system_variables['battery'] > 0)
        Invariants('system_armed', lambda : system_variables['armed'] == True, 'description')
        Invariants('altitude', lambda : system_variables['altitude'] > -0.3, 'description')
    ],
    # Postconditions
    [
        # get sv from parameters
        Postcondition('altitude', lambda sv: sv['alt'] - 0.3 < system_variables['altitude'] < sv['alt'] + 0.3)
        Postcondition('battery', lambda : system_variables['battery'] > 0 )
        Postcondition('time', lambda : max_expected_time > time.time() - system_variables['time'])

    ]
)

action['land'] = Action(
    # Description
    'Commands the system to go to a specific location.',

    # Preconditions
    [
        # get sv from parameters, I think there's no need for lambdas here
        Precondition('battery', lambda : system_variables['battery'] >= max_expected_battery_usage\
        (None, None, 0), 'description')
        Precondition('altitude', lambda : system_variables['altitude'] > 0.3, 'description')
        Precondition('armed', lambda : system_variables['armed'] == True, 'description')
    ],
    # Invariants
    [
        Invariants('battery', lambda : system_variables['battery'] > 0)
    ],
    # Postconditions
    [
        # get sv from parameters
        Postcondition('altitude', lambda : system_variables['altitude'] < 0.3, 'description')
        Postcondition('battery', lambda : system_variables['battery'] > 0, 'description')
        Postcondition('time', lambda : max_expected_time(None, None, 0) > time.time() - system_variables['time'], 'description')
        Precondition('armed', lambda : system_variables['armed'] == False, 'description')
    ]
)

action['takeoff'] = Action(
    # Description
    'Commands the system to go to a specific location.',
    # Parameters
    [
        Parameter('altitude', float, 'description')
    ],
    # Preconditions
    [
        # get sv from parameters, I think there's no need for lambdas here
        Precondition('battery', lambda sv: system_variables['battery'] >= max_expected_battery_usage\
        (None, None, sv['altitude']), 'description')
        Precondition('altitude', lambda : system_variables['altitude'] < 0.3, 'description')
        Precondition('armed', lambda : system_variables['armed'] == True, 'description')
    ],
    # Invariants
    [
        Invariants('system_armed', lambda : system_variables['armed'] == True, 'description')
        Invariants('altitude', lambda : system_variables['altitude'] > -0.3, 'description')
    ],
    # Postconditions
    [
        # get sv from parameters
        Postcondition('altitude', lambda sv: sv['alt'] - 0.3 < system_variables['altitude'] < sv['alt'] + 0.3)
        Postcondition('battery', lambda : system_variables['battery'] > 0 )
        Postcondition('time', lambda : max_expected_time > time.time() - system_variables['time'])
        Postcondition('time', lambda sv: )
    ]
)

def read_variable(variable):
    return system_variables[variable]()

def max_expected_battery_usage(prime_latitude, prime_longitude, prime_altitude):
    distance = distance.great_circle((system_variables['latitude'], \
        system_variables['longitude']), (prime_latitude, prime_longitude))
    standard_dev, mean  = get_standard_deviation_and_mean(SAMPLE_BATTERY)
    return (mean + standard_dev + WINDOW_BATTERY) * distance


def max_expected_time(prime_latitude, prime_longitude, prime_altitude):
    distance = distance.great_circle((system_variables['latitude'], \
        system_variables['longitude']), (prime_latitude, prime_longitude))
    standard_dev, mean  = get_standard_deviation_and_mean(SAMPLE_TIME)
    return (mean + standard_dev + WINDOW_BATTERY) * distance


def get_standard_deviation_and_mean(sample):
    return statistics.stdev(sample), numpy.mean(sample)



class Action(object):
    """docstring for Action."""
    def __init__(self, parameters, precondition, invariants, postconditions):
        self.parameters = parameters
        self.precondition = precondition
        self.invariants = invariants
        self.postconditions = postconditions
        self.arg = arg

class Invariant(object):
    """docstring for Postcondition."""
    def __init__(self, _type, value, description):
        self._type = _type
        self.value = value
        self.description


class Postcondition(object):
    """docstring for Postcondition."""
    def __init__(self, _type, value, description):
        self._type = _type
        self.value = value
        self.description


class Precondition(object):
    """docstring for Precondition."""
    def __init__(self, _type, value, description):
        self._type = _type
        self.value = value
        self.description


class Parameter(object):
    """docstring for ."""
    def __init__(self, _type, value, description):
        self._type = _type
        self.value = value
        self.description
