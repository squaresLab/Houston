class System(object):

    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


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


class Predicate(object):

    def __init__(self, predicate):
        self._predicate = predicate


    def check(self, action):
        return self._predicate(action)


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
        self._predicate = predicate


class Precondition(Predicate):
    """docstring for Precondition."""
    def __init__(self, name, description, predicate):
        self.__name = name
        self.__description = description
        self._predicate = predicate


class Parameter(object):
    """docstring for ."""
    def __init__(self, typ, value, description):
        self.__type = typ
        self.__value = value
        self._description = description

    def get_value():
        return self.__value
