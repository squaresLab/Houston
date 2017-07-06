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


class System(object):

    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


class ArduPilot(System):

    def __init__(self):
        variables = {}
        variables['time'] = SystemVariable('time', lambda: time.time())
        variables['altitude'] = SystemVariable('altitude',
            lambda: rospy.client.wait_for_message('/mavros/local_position/odom',
                Odometry, timeout=1.0).pose.pose.position.z)
        variables['latitude'] = SystemVariable('latitude',
            lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                NavSatFix, timeout=1.0).latitude)
        variables['longitude'] = SystemVariable('longitude',
            lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                NavSatFix, timeout=1.0).longitude)
        variables['battery'] = SystemVariable('battery',
            lambda: rospy.client.wait_for_message('/mavros/battery',
                BatteryStatus, timeout=1.0).remaining)
        variables['armed'] = SystemVariable('arm',
                lambda : rospy.client.wait_for_message('/mavros/state',
                    State, timeout=1.0).armed)
        variables['mode'] = SystemVariable('mode',
                lambda : rospy.client.wait_for_message('/mavros/state',
                    State, timeout=1.0).mode)


        schemas = {}
        schemas['goto'] = GoToActionSchema()
        schemas['takeoff'] = TakeoffActionSchema()
        schemas['land'] = LandActionSchema()
        schemas['arm'] = ArmActionSchema()
        schemas['mode'] = SetModeActionSchema()




        super(ArduPilot, self).__init__(variables, schemas)


"""
Description of system variables goes here!

* How do we use them?
* What are they for?
"""
class SystemVariable(object):

    """
    Constructs a new system variable
    """
    def __init__(self, name, getter):
        self.__name = name
        self.__getter = getter

    """
    Returns the name of this system variable
    """
    def name(self):
        return self.__name

    """
    Inspects the current state of this system variable
    """
    def read(self):
        return self.__getter()


class ActionSchema(object):
    """docstring for Action."""
    def __init__(self, name, parameters, precondition, invariants, postconditions):
        self.__name           = name
        self.__parameters     = parameters
        self.__precondition   = precondition
        self.__invariants     = invariants
        self.__postconditions = postconditions


    def dispatch(self, parameters):
        " do the mission!"
        return


    def satisfied(self, action):
        return all(p.check(action) for p in self.__postconditions)


"""
A description of arm
"""
class ArmActionSchema(ActionSchema):
    """docstring for ArmActionSchema."""
    def __init__(self):
        preconditions = [
            Precondition('armed', 'description',
                         lambda sv: sv['armed'].read() == False)
        ]
        postconditions = [
            Postcondition('armed', 'description',
                         lambda sv: sv['armed'].read() == True)
        ]
        invariants = [
            Invariant('battery', 'description',
                      lambda sv: sv['battery'].read() > 0)
        ]
        super(ArmActionSchema, self).__init__('arm', None, preconditions, invariants, postconditions)

    def dispatch():
        arm = rospy.ServiceProxy('/mavros/cmd/arming', CommandBool)
        arm(True)


"""
A description of set mode
"""
class SetModeActionSchema(ActionSchema):
    """docstring for SetModeActionSchema"""
    def __init__(self):
        parameters = [
            Parameter('mode', str, 'description')
        ]
        postconditions = [
            Postcondition('mode', 'description',
                          lambda sv: sv['mode'].read() == parameters[0].get_value())
        ]
        invariants = [
            Invariant('battery', 'description',
                      lambda sv: sv['battery'].read() > 0)
        ]
        super(SetModeActionSchema, self).__init__('setmode', parameters, None, invariants, postconditions)

    def dispatch(parameters):
        set_mode = rospy.ServiceProxy('/mavros/set_mode', SetMode)
        set_mode(0, parameters.read())


"""
A description of goto
"""
class GoToActionSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('latitude', float, 'description'),
            Parameter('longitude', float, 'description'),
            Parameter('altitude', float, 'description')
        ]

        preconditions = [

            Precondition('battery', 'description',
                         lambda sv: sv['battery'].read() >= max_expected_battery_usage(
                         parameters[0].get_value(),
                         parameters[1].get_value(),
                         parameters[2].get_value())),
            Precondition('altitude', 'description',
                         lambda sv: sv['altitude'].read() > 0)
        ]

        invariants = [
            Invariant('battery', 'description',
                       lambda sv: sv['battery'].read() > 0),
            Invariant('system_armed', 'description',
                       lambda sv: sv['armed'].read() == True),
            Invariant('altitude', 'description',
                       lambda sv: sv['altitude'].read() > -0.3)
        ]

        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['alt'].read() - 0.3 < \
                            parameters[2].get_value() < sv['alt'].read() + 0.3),
            Postcondition('battery', 'description',
                          lambda sv: sv['battery'].read() > 0 ),
            Postcondition('time', 'description',
                          # we need a "start" time (or an initial state)
                          lambda sv: time.time() - sv['time'].read() <
                          max_expected_time(
                            parameters[0].get_value(),
                            parameters[1].get_value(),
                            parameters[2].get_value()))
        ]

        super(GoToActionSchema, self).__init__('goto',parameters, preconditions, invariants, postconditions)


    def dispatch(parameters):
        return
        #roscall()
        # TODO


"""
A description of land
"""
class LandActionSchema(ActionSchema):
    def __init__(self):
        preconditions = [
            Precondition('battery', 'description',
                lambda sv: sv['battery'].read() >= \
                    max_expected_battery_usage(None, None, 0)),
            Precondition('altitude', 'description',
                lambda sv: sv['altitude'].read() > 0.3),
            Precondition('armed', 'description',
                lambda sv: sv['armed'].read() == True)
        ]
        invariants = [
            Invariant('battery', 'description',
                       lambda sv: sv['battery'].read() > 0),
            Invariant('altitude', 'description',
                       lambda sv: sv['altitude'].read() > -0.3)
        ]
        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['altitude'].read() < 0.3 ),
            Postcondition('battery', 'description',
                          lambda sv: sv['battery'].read() > 0 ),
            Postcondition('time', 'description',
                          # we need a "start" time (or an initial state)
                          lambda sv: max_expected_time(None, None, 0) > \
                            time.time() - sv['time'])
        ]
        super(LandActionSchema, self).__init__('land', None, preconditions, invariants, postconditions)


    def dispatch():
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        land(0, 0, 0, 0, 0)


"""
A description of takeoff
"""
class TakeoffActionSchema(ActionSchema):
    """docstring for TakeoffActionSchema."""
    def __init__(self):
        parameters = [
            Parameter('altitude', float, 'description')
        ]
        preconditions = [
            Precondition('battery', 'description',
                         lambda sv: sv['battery'].read() >= \
                         max_expected_battery_usage(
                            None,
                            None,
                            sv['altitude'].get_value())),
            Precondition('altitude', 'description',
                         lambda sv: sv['altitude'].read() < 0.3),
            Precondition('armed', 'description',
                         lambda sv: sv['armed'].read() == True)
        ]
        invariants = [
            Invariant('armed', 'description',
                      lambda sv: sv['armed'].read() == True),
            Invariant('altitude', 'description',
                      lambda sv: sv['altitude'].read() > -0.3)
        ]
        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['alt'].read() - 0.3 < \
                          parameters[0].get_value() < sv['alt'].read() + 0.3)
        ]

    def dispatch(parameters):
      takeoff = rospy.ServiceProxy('/mavros/cmd/takeoff', CommandTOL)
      takeoff(0, 0, 0, 0, parameters[0].read())


class Predicate(object):

    def __init__(self, predicate):
        self.__predicate = predicate


    def check(self, action):
        return self.__predicate(action)


class Invariant(Predicate):
    """docstring for Postcondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__predicate = predicate
        self.__description = description


class Postcondition(Predicate):
    """docstring for Postcondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__description = description
        self.__predicate = predicate


class Precondition(Predicate):
    """docstring for Precondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__description = description
        self.__predicate = predicate


class Parameter(object):
    """docstring for ."""
    def __init__(self, typ, value, description):
        self.__type = typ
        self.__value = value
        self.__description = description

    def get_value():
        return self.__value


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


if __name__ == "__main__":
    ar = ArduPilot()
