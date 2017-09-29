import copy
import json
import math
import houston.action


class State(object):
    """
    Describes the state of the system at a given moment in time, in terms of
    its internal and external variables.
    """
    @staticmethod
    def from_file(fn):
        """
        Constructs a system state from a given file, containing a JSON-based
        description of its contents.

        :param  fn  the path to the state description file

        :returns    the corresponding State for that file
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        return State.from_json(jsn)


    @staticmethod
    def from_json(jsn):
        """
        Constructs a description of a state from its JSON description.
        """
        assert ('variables' in jsn)
        assert isinstance(jsn['variables'], dict)
        return State(jsn['variables'])


    def __init__(self, values, time_offset):
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """

        assert isinstance(time_offset, float)

        self.__values = copy.copy(values)
        self.__time_offset = time_offset

    
    @property
    def values(self):
        """
        Returns the values of each of the state variables as a dictionary,
        indexed by name.
        """
        return copy.copy(self.__values)

    @property
    def time_offset(self):
        return self.__time_offset


    def __getitem__(self, variable):
        """
        :see `read`
        """
        return self.read(variable)


    def read(self, variable):
        """
        Returns the value for a given state variable
        """
        return self.__values[variable]


    def dump(self):
        """
        Prints this state to the standard output.
        """
        for variable in self.__values:
            print('Variable: {} - State: {}'.format(variable, self[variable]))


    def to_json(self):
        """
        Returns a JSON description of this state.
        """
        return {
            'variables': copy.copy(self.__values)
        }


    def __str__(self):
        return str(self.to_json())


    def __repr__(self):
        return str(self)


class StateVariable(object):

    def __init__(self, name, getter, noise=None):
        """
        Constructs a new state variable

        :param  name:   the name of this variable
        :param  type:   the type of this variable
        :param  getter: a lambda function, used to obtain the value of this variable
        :param  noise:  the inherent level of noise when measuring this variable
        """
        assert (isinstance(self, InternalVariable) or isinstance(self, ExternalVariable))
        assert (noise is None or type(noise) in [float, int])
        assert (noise is None or noise >= 0)

        self.__name = name
        self.__getter = getter
        self.__noise = noise


    """
    Returns true if there is inherent noise in the measurement of this variable.
    """
    @property
    def is_noisy(self):
        return self.__noise is not None


    """
    Returns the inherent level of noise that is to be expected when measuring
    this variable. If no noise is expected, None is returned.
    """
    @property
    def noise(self):
        return self.__noise


    """
    Returns the name of this system variable
    """
    @property
    def name(self):
        return self.__name

    
    def eq(self, x, y):
        """
        Determines whether two measurements of this state variable are
        considered to be equal.
        """
        if not self.is_noisy:
            return x == y

        d = math.fabs(x - y)
        return d <= self.__noise


    def neq(self, x, y):
        """
        Determines whether two measurements of this state variable are not
        considered to be equal.
        """
        return not self.eq(x, y)

    
    def gt(self, x, y):
        return x > y

    
    def lt(self, x, y):
        return x < y


    def leq(self, x, y):
        return not self.gt(x, y)


    def geq(self, x, y):
        return not self.lt(x, y)


    """
    Inspects the current state of this system variable
    """
    def read(self):
        return self.__getter()


class InternalVariable(StateVariable):
    """
    Internal variables describe the internal state of a given system.
    (i.e., they represent a system's knowledge of itself and its surroundings.)
    A user-provided lambda function is used to inspect the value of the state
    variable at any given time.
    """
    pass


class ExternalVariable(StateVariable):
    """
    TODO
    """
    pass


class Environment(object):
    @staticmethod
    def fromFile(fn):
        """
        Constructs a system environment from a given file, containing a JSON-based
        description of its contents.

        :param  fn  the path to the state description file

        :returns    the corresponding en for that file
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        return Environment.from_json(jsn)


    @staticmethod
    def from_json(jsn):
        """
        Constructs a description of an environment from its JSON description.
        """
        assert ('constants' in jsn)
        assert isinstance(jsn['constants'], dict)
        return Environment(jsn['constants'])

    """
    Holds a description of an environment in which a mission should be conducted.
    """

    def __init__(self, values):
        """
        Constructs a description of a mission environment.

        :param  values: a dictionary of environment constant values, indexed
                        by the name of those constants.
        """
        self.__values = copy.copy(values)


    def __getattr(self, variable):
        return self.read(variable)


    def read(self, variable):
        """
        Returns the value of a given environment constant.
        """
        return self.__values[variable]


    def to_json(self):
        """
        Returns this environment description as a JSON object (i.e., a dict)
        """
        return {
            'constants': copy.copy(self.__values)
        }
