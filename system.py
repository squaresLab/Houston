"""
Description of system variables goes here!

* How do we use them?
* What are they for?
"""
class SystemVariable(object):

    """
    Constructs a new system variable
    """
    def __init__(self, getter):
        self.__getter = getter

    """
    Inspects the current state of this system variable
    """
    def read(self):
        return self.__getter()

class ActionSchema(object):
    """docstring for Action."""
    def __init__(self, parameters, precondition, invariants, postconditions, dispatch):
        self.parameters = parameters
        self.precondition = precondition
        self.invariants = invariants
        self.postconditions = postconditions

    def dispatch(parameters):
        " do the mission!"
        return


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
    def __init__(self, typ, value, description):
        self.__type = typ
        self.__value = value
        self.__description

    def get_value():
        return self.__value
