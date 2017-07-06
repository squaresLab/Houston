"""
docstring
"""
class System(object):

    def __init__(self, variables, schemas):
        self.__variables = variables
        self.__schemas = schemas


class SystemState(object):

    def __init__(self, values):
        


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


"""

"""
class Mission(object):
    
    
    def __init__(self, environment, initial, actions):
        assert(actions != [])
        self.__environment = environment
        self.__initial = initial
        self.__actions = actions


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
