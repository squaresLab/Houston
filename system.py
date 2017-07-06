"""
docstring
"""
class System(object):

    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


class InternalState(object):
    """
    Describes the internal state of a robot in terms of its internal state
    variables.
    """

    def __init__(self, values):
        self.__values = values


    def read(variable):
        """
        Returns the value for a given (internal) state variable
        """
        return self.__values[variable]


class InternalStateVariable(object):
    """
    Internal variables describe the internal state of a given system.
    (i.e., they represent a system's knowledge of itself and its surroundings.)
    """

    def __init__(self, name, getter):
        pass


class Environment(object):
    """
    Holds a description of an environment in which a mission should be conducted.
    """

    pass


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

"""
Hello.
"""
class ActionSchema(object):
    def __init__(self, name, parameters, precondition, invariants, postconditions):
        self.__name           = name
        self.__parameters     = parameters
        self.__precondition   = precondition
        self.__invariants     = invariants
        self.__postconditions = postconditions


    def dispatch(self, parameters):
        raise UnimplementedError


    def satisfied(self, action):
        return all(p.check(action) for p in self.__postconditions)

"""
Hello.
"""
class Predicate(object):

    def __init__(self, predicate):
        self.__predicate = predicate


    def check(self, action):
        return self.__predicate(action)


"""
Hello.
"""
class Invariant(Predicate):
    def __init__(self, name, description, predicate):
        super(Predicate, self).__init__(predicate)
        self.__name = name
        self.__description = description


"""
Hello.
"""
class Postcondition(Predicate):
    def __init__(self, name, description, predicate):
        super(Predicate, self).__init__(predicate)
        self.__name = name
        self.__description = description


"""
Hello.
"""
class Precondition(Predicate):
    def __init__(self, name, description, predicate):
        super(Predicate, self).__init__(predicate)
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
