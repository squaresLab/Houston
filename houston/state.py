from typing import Dict, Any, Optional, Union

import copy
import json
import math


class State(object):
    """
    Describes the state of the system at a given moment in time, in terms of
    its internal and external variables.
    """
    @staticmethod
    def from_file(fn: str) -> 'State':
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
    def from_json(jsn: Dict[str, Any]) -> 'State':
        return State(jsn['variables'], jsn['time_offset'])

    def __init__(self,
                 values: Dict[str, Any],
                 time_offset: float
                 ) -> None:
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """
        self.__values = values.copy()
        self.__time_offset = time_offset

    @property
    def values(self) -> Dict[str, Any]:
        """
        Returns the values of each of the state variables as a dictionary,
        indexed by name.
        """
        return copy.copy(self.__values)

    @property
    def time_offset(self) -> float:
        return self.__time_offset

    def __getitem__(self, variable: str) -> Any:
        """
        See `read`
        """
        return self.read(variable)

    def read(self, variable: str) -> Any:
        """
        Returns the value for a given state variable
        """
        return self.__values[variable]

    # FIXME get rid of this
    def dump(self) -> None:
        """
        Prints this state to the standard output.
        """
        for variable in self.__values:
            m = 'Variable: {} - State: {}'
            m = m.format(variable, self[variable])
            print(m)

    def to_json(self) -> Dict[str, Any]:
        """
        Returns a JSON description of this state.
        """
        return {'variables': self.__values.copy(),
                'time_offset': self.__time_offset}

    def __repr__(self) -> str:
        vrs = ["{}: {}".format(k, repr(v)) for (k, v) in self.__values.items()]
        s_vrs = '; '.format(vrs)
        s = "State(time_offset={:.3f}, variables={})"
        s = s.format(self.time_offset, s_vrs)
        return s


class Variable(object):
    def __init__(self,
                 name: str,
                 getter,  # FIXME add annotation
                 noise: Optional[Union[int, float]] = None
                 ) -> None:
        """
        Constructs a new state variable

        Parameters:
            name: the name of this variable.
            type: the type of this variable.
            getter: a lambda function, used to obtain the value of this
                variable.
            noise: the inherent level of noise when measuring this variable.
        """
        assert noise is None or noise >= 0
        self.__name = name
        self.__getter = getter
        self.__noise = noise

    @property
    def is_noisy(self) -> bool:
        return self.__noise is not None

    @property
    def noise(self) -> Optional[Union[int, float]]:
        """
        The inherent level of noise that is to be expected when measuring
        this variable. If no noise is expected, None is returned.
        """
        return self.__noise

    """
    Returns the name of this system variable
    """
    @property
    def name(self) -> str:
        return self.__name

    def eq(self, x, y) -> bool:
        """
        Determines whether two measurements of this state variable are
        considered to be equal.
        """
        if not self.is_noisy:
            return x == y

        d = math.fabs(x - y)
        return d <= self.__noise

    def neq(self, x, y) -> bool:
        """
        Determines whether two measurements of this state variable are not
        considered to be equal.
        """
        return not self.eq(x, y)

    def gt(self, x, y) -> bool:
        return x > y

    def lt(self, x, y) -> bool:
        return x < y

    def leq(self, x, y) -> bool:
        return not self.gt(x, y)

    def geq(self, x, y) -> bool:
        return not self.lt(x, y)

    def read(self, sandbox):
        """
        Inspects the current state of this system variable
        """
        return self.__getter(sandbox)


class Environment(object):
    @staticmethod
    def from_file(fn: str) -> 'Environment':
        """
        Loads an environment description from a given file.

        Returns:
            the environment described in the file.
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        return Environment.from_json(jsn)

    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'Environment':
        return Environment(jsn['constants'])

    def __init__(self, values: Dict[str, Any]) -> None:
        """
        Constructs a description of a mission environment.

        Parameters:
            values: a dictionary of environment constant values, indexed by
                the name of those constants.
        """
        self.__values = values.copy()

    def __getattr(self, variable: str):
        return self.read(variable)

    def read(self, variable: str):
        """
        Returns the value of a given environment constant.
        """
        return self.__values[variable]

    def to_json(self) -> Dict[str, Any]:
        return {'constants': self.__values.copy()}
