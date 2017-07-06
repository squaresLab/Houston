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
        schemas['takeoff'] = TakeOffActionSchema()
        schemas['land'] = LandActionSchema()
        schemas['arm'] = ArmActionSchema()
        schemas['mode'] = ModeActionSchema()




        super().__init__(variables, schemas)

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
    def __init__(self, parameters, precondition, invariants, postconditions):
        self.__parameters = parameters
        self.__precondition = precondition
        self.__invariants = invariants
        self.__postconditions = postconditions


    def dispatch(self, parameters):
        " do the mission!"
        return


    def satisfied(self, action):
        return all(p.check(action) for p in self.__postconditions)

"""
A description of arme
"""
class ArmActionSchema(ActionSchema):
    """docstring for ArmActionSchema."""
    def __init__(self):
        preconditions = [
            Precondition('armed', 'description',
                         lambda sv: sv['armed'] == False)
        ]
        postconditions = [
            Postcondition('armed', 'description',
                         lambda sv: sv['armed'] == True)
        ]
        invariants = [
            Invariant('battery', 'description',
                      lambda sv: sv['battery'] > 0)
        ]
    def dispatch():
        arm = rospy.ServiceProxy('/mavros/cmd/arming', CommandBool)
        arm(True)

class SetModeActionSchema(ActionSchema):
    """docstring for SetModeActionSchema"""
    def __init__(self):
        parameters = [
            Parameter('mode', str)
        ]
        postconditions = [
            Postcondition('mode', 'description',
                          lambda sv: sv['mode'] == parameters[0])
        ]
        invariants = [
            Invariant('battery', 'description',
                      lambda sv: sv['battery'] > 0)
        ]
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
                         lambda sv: sv['battery'] >= max_expected_battery_usage(parameters[0], parameters[1], parameters[2])),
            Precondition('altitude', 'description',
                         lambda sv: sv['altitude'] > 0)
        ]

        invariants = [
            Invariant('battery', 'description',
                       lambda sv: sv['battery'] > 0),
            Invariant('system_armed', 'description',
                       lambda sv: sv['armed'] == True),
            Invariant('altitude', 'description',
                       lambda sv: sv['altitude'] > -0.3)
        ]

        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['alt'] - 0.3 < parameters[2] < sv['alt'] + 0.3),
            Postcondition('battery', 'description',
                          lambda sv: sv['battery'] > 0 ),
            Postcondition('time', 'description',
                          # we need a "start" time (or an initial state)
                          lambda sv: max_expected_time > time.time() - sv['time'])
        ]

        super().__init__('goto', parameters, preconditions, invariants, postconditions)


    def dispatch(parameters):
        roscall()

"""
A description of land
"""

class LandActionSchema(ActionSchema):
    def __init__(self):
        preconditions = [   # get sv from parameters, I think there's no need for lambdas here
            Precondition('battery', 'description',
                lambda sv: sv['battery'] >= max_expected_battery_usage(None, None, 0)),
            Precondition('altitude', 'description',
                lambda sv: sv['altitude'] > 0.3),
            Precondition('armed', 'description',
                lambda sv: sv['armed'] == True)
        ]
        invariants = [
            Invariant('battery', 'description',
                       lambda sv: sv['battery'] > 0),
            Invariant('altitude', 'description',
                       lambda sv: sv['altitude'] > -0.3)
        ]
        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['altitude'] < 0.3 ),
            Postcondition('battery', 'description',
                          lambda sv: sv['battery'] > 0 ),
            Postcondition('time', 'description',
                          # we need a "start" time (or an initial state)
                          lambda sv: max_expected_time > time.time() - sv['time'])
        ]
        super().__init__('land', parameters, preconditions, invariants, postconditions)


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
                         lambda sv: sv['battery'] >= max_expected_battery_usage(None, None, sv['altitude'])),
            Precondition('altitude', 'description',
                         lambda sv: sv['altitude'] < 0.3),
            Precondition('armed', 'description',
                         lambda sv: sv['armed'] == True)
        ]
        invariants = [
            Invariant('armed', 'description',
                      lambda sv: sv['armed'] == True),
            Invariant('altitude', 'description',
                      lambda sv: sv['altitude'] > -0.3)
        ]
        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['alt'] - 0.3 < parameters[0].read() < sv['alt'] + 0.3)
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
        self.__description

    def get_value():
        return self.__value
