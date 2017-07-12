import thread
import time
class System(object):
    """
    Description of System.
    """


    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


    def setUp(self, mission):
        """
        Responsible for appropriately configuring and launching the system,
        for a given mission.
        """
        raise NotImplementedError


    def tearDown(self, mission):
        """
        Responsible for safely closing the system, following the execution of
        a given mission.
        """
        raise NotImplementedError


    def execute(self, mission):
        self.setUp(mission)
        self.executeActions(mission)

    def executeActions(self, mission):

        for action in mission.getActions():
            actionType = action.get_type()
            print actionType
            # check for preconditions
            if self.__schemas[actionType].satisfiedPreconditions(self.__variables,
                action.get_values()):
                self.__schemas[actionType].dispatch(action.get_values())
                while not self.__schemas[actionType].satisfiedPostConditions(self.__variables,
                    action.get_values()) and \
                    self.__schemas[actionType].satisfiedInvariants(self.__variables,
                    action.get_values()):
                        pass
        self.tearDown(mission)


    def getInternalState(self):
        # TODO
        vals = {}
        return InternalState(vals)

#        print '---'
#        print 'Mode: {}'.format(self.variables['mode'].read())
#        print 'Altitude: {}'.format(self.variables['altitude'].read())
#        print 'Longitude: {}'.format(self.variables['longitude'].read())
#        print 'Latitude: {}'.format(self.variables['latitude'].read())
#        print 'Battery: {}'.format(self.variables['battery'].read())
#        print 'Armed: {}'.format(self.variables['armed'].read())
#        print 'Armable: {}'.format(self.variables['armable'].read())
#        print '---'

class State(object):
    """
    Describes the internal or external state of the system in terms of its
    internal or external variables.
    """


    def __init__(self, values):
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """
        self.__values = values


    def read(variable):
        """
        Returns the value for a given state variable
        """
        return self.__values[variable]


class InternalState(State):
    """
    Describes the state of the system in terms of its internal state
    variables.
    """
    pass


class ExternalState(State):
    """
    Describes the state of the system in terms of its external state
    variables.
    """
    pass


class StateVariable(object):

    def __init__(self, name, getter):
        """
        Constructs a new state variable

        :param  name:   the name of this variable
        :param  type:   the type of this variable
        :param  getter: a lambda function, used to obtain the value of this variable
        """
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


class InternalStateVariable(StateVariable):
    """
    Internal variables describe the internal state of a given system.
    (i.e., they represent a system's knowledge of itself and its surroundings.)
    A user-provided lambda function is used to inspect the value of the state
    variable at any given time.
    """

    def __init__(self, name, getter):
        super(InternalStateVariable, self).__init__(name, getter)


class Environment(object):
    """
    Holds a description of an environment in which a mission should be conducted.
    """

    def __init__(self, values):
        """
        Constructs a description of a mission environment.

        :param  values: a dictionary of environment variable values, indexed
                        by the name of those variables.
        """
        self.__values = values

    def read(self, variable):
        """
        Returns the value of a given environment variable.
        """
        return self.__values[variable]


class Mission(object):
    """
    A mission is represented as a sequence of actions that are carried out in
    a given environment and initial state.
    """

    def __init__(self, environment, internal, external, actions):
        """
        Constructs a new Mission description.

        :param  environment:    a description of the environment
        :param  internal:       a description of the initial internal state
        :param  external:       a description of the initial external state
        :param  actions:        a list of actions
        """
        assert(actions != [])
        assert(isinstance(environment, Environment) and not environment is None)
        assert(isinstance(internal, InternalState) and not internal is None)
        assert(isinstance(external, ExternalState) and not external is None)

        self.__environment = environment
        self.__internal = internal
        self.__external = external
        self.__actions = actions

    def getEnvironment(self):
        return self.__environment

    def getInitialInternalState(self):
        return self.__internal

    def getInitialExternalState(self):
        return self.__external

    def getActions(self):
        return self.__actions

class Action(object):
    def __init__(self, _type, values):
        self.__type = _type
        self.__values = values

    def get_type(self):
        return self.__type

    def get_value(self, value):
        return self.__values[value]

    def get_values(self):
        return self.__values

"""
Hello.
"""
class ActionSchema(object):
    def __init__(self, name, parameters, precondition, invariants, postconditions):
        self.__name           = name
        self.__parameters     = parameters
        self.__preconditions   = precondition
        self.__invariants     = invariants
        self.__postconditions = postconditions


    def dispatch(self, parameters):
        raise UnimplementedError


    def satisfiedPostConditions(self, system_variables, parameters):
        return all(p.check(system_variables, parameters) for p in self.__postconditions)

    def satisfiedPreconditions(self, system_variables, parameters):
        print 'Doing precondition params: {} '.format(parameters)
        print all(p.check(system_variables, parameters) for p in self.__preconditions)
        return all(p.check(system_variables, parameters) for p in self.__preconditions)

    def satisfiedInvariants(self, system_variables, parameters):
        return all(p.check(system_variables, parameters) for p in self.__invariants)

"""
Hello.
"""
class Predicate(object):

    def __init__(self, name, predicate):
        self.__name = name
        self.__predicate = predicate


    def check(self, system_variables, parameters):
        return self.__predicate(system_variables, parameters)


"""
Hello.
"""
class Invariant(Predicate):
    def __init__(self, name, description, predicate):
        super(Invariant, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


"""
Hello.
"""
class Postcondition(Predicate):
    def __init__(self, name, description, predicate):
        super(Postcondition, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


"""
Hello.
"""
class Precondition(Predicate):
    def __init__(self, name, description, predicate):
        super(Precondition, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


"""
Hello.
"""
class Parameter(object):
    """docstring for ."""
    def __init__(self, typ, value, description):
        self.__type = typ
        self.__value = value
        self._description = description


    def get_value():
        return self.__value
