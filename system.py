class System(object):

    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas

class ArduPilot(System):

    def __init__(self):
        variables = [
            SystemVariable('time', 
                lambda: time.time()),
            SystemVariable('altitude',
               lambda: rospy.client.wait_for_message('/mavros/local_position/odom',
                                                    Odometry,
                                                    timeout=1.0).pose.pose.position.z),
            SystemVariable('latitude',
                lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                                                       NavSatFix,
                                                       timeout=1.0).latitude),
            SystemVariable('longitude',
                lambda: rospy.client.wait_for_message('/mavros/global_position/global',
                                                      NavSatFix,
                                                      timeout=1.0).longitude),
            SystemVariable('battery',
                lambda: rospy.client.wait_for_message('/mavros/battery',
                                                      BatteryStatus,
                                                      timeout=1.0).remaining),
            SystemVariable('arm',
                lambda : rospy.client.wait_for_message('/mavros/state',
                                                       State,
                                                       timeout=1.0).armed),
            SystemVariable('mode',
                lambda : rospy.client.wait_for_message('/mavros/state',
                                                       State,
                                                       timeout=1.0).mode)
        ]

        schemas = []
        schemas.append(ActionSchema('goto', 'Commands the system to go to a specific location.',
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
        ))



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
            # get sv from parameters, I think there's no need for lambdas here
            Precondition('battery', 'description',
                         lambda sv: sv['battery'] >= max_expected_battery_usage(sv['latitude'], sv['longitude'], sv['altitude']))
            Precondition('altitude', 'description',
                         lambda sv: sv['altitude'] > 0)
        ]

        invariants = [
            Invariant('battery', 'description',
                       lambda sv: sv['battery'] > 0)
            Invariant('system_armed', 'description',
                       lambda sv: sv['armed'] == True)
            Invariant('altitude', 'description',
                       lambda sv: sv['altitude'] > -0.3)
        ]
        
        postconditions = [
            Postcondition('altitude', 'description',
                          lambda sv: sv['alt'] - 0.3 < sv['altitude'] < sv['alt'] + 0.3)
            Postcondition('battery', 'description',
                          lambda sv: sv['battery'] > 0 )
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
class 
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



class Invariant(object):
    """docstring for Postcondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__predicate = predicate
        self.__description = description


class Postcondition(object):
    """docstring for Postcondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__description = description
        self.__predicate = predicate


class Precondition(object):
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
