import copy
import json
import action


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
        print jsn.keys()
        return State.from_json(jsn)


    @staticmethod
    def from_json(jsn):
        """
        Constructs a description of a state from its JSON description.
        """
        assert ('variables' in jsn)
        assert isinstance(jsn['variables'], dict)
        return State(jsn['variables'])


    def __init__(self, values):
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """
        self.__values = copy.copy(values)

    
    @property
    def values(self):
        """
        Returns the values of each of the state variables as a dictionary,
        indexed by name.
        """
        return copy.copy(self.__values)


    def __getattr__(self, variable):
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


class ExpectedStateValue(object):

    def __init__(self, value, noise=None):
        """
        Constructs a description of an expected.
        """
        assert (isinstance(noise, float) or isinstance(noise, int) or noise is None)
        assert (noise is None or type(value) == type(noise))

        self.__value = value
        self.__noise = noise


    def is_expected(self, observed, measurement_noise):
        assert (observed is not None)
        assert (measurement_noise is None or type(measurement_noise) == type(observed))

        # add the measurement noise to the action noise
        if measurement_noise is None:
            noise = self.__noise
        elif self.__noise is not None:
            noise = self.__noise + measurement_noise
        else:
            noise = measurement_noise

        # check the observed value against the expected range
        if noise is None:
            return self.__value == observed
        else:
            return (self.__value - noise) < observed < (self.__value + noise)


class ExpectedState(object):

    @staticmethod
    def identical(to):
        """
        Returns an ExpectedState object that is identical to a given State.
        """
        expected = {}
        for (name, val) in to.values.items():
            expected[name] = ExpectedStateValue(val)
        return ExpectedState(expected)


    def __init__(self, values):
        """
        Constructs a description of an expected state of the system.
        """
        assert (isinstance(values, dict))
        self.__values = values


    def is_expected(self, variables, st):
        """
        :param  variables:      a dictionary containing the definitions of \
                                the variables for the system under test, \
                                indexed by their names
        :param  st:             the observed state of the system

        :returns    True if the observed state of the system was expected
        """
        assert (all(isinstance(k, str) for k in variables))
        assert (all(isinstance(v, StateVariable) for v in variables.values()))
        assert isinstance(variables, dict)
        assert isinstance(st, State)

        for (name, expected_value) in self.values.items():
            measurement_noise = variables[name].noise
            if not expected_value.is_expected(st[name], measurement_noise):
                return False

        return True


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


class Estimator(object):
    """
    Estimates the expected state of a given variable after the execution of an
    action.
    """

    def __init__(self, variable, func, noise_func = None):
        """
        Constructs an estimator for a given state variable.

        :param  variable    the name of the (estimated) state variable
        :param  func        a lambda function responsible for calculating \
                            the expected value of the associated variable \
                            after the execution of an action.
        :param  noiseFunc   an (optional) lambda function responsible for \
                            calculating the permitted amount of noise in the \
                            expected value produced by this estimator
        """
        assert isinstance(variable, str)
        assert (callable(func))
        assert (callable(noise_func) or noise_func is None)

        self.__variable = variable
        self.__func = func
        self.__noise_func = noise_func


    @property
    def variable_name(self):
        """
        The name of the variable that is being estimated.
        """
        return self.__variable


    def compute_expected_value(self, act, state, environment):
        """
        Computes the expected value for the variable associated with this estimator,
        within a given state and environment.

        :param  act:    action used to calculate the expected state.
        :param  state:  the state of the system immediately prior to \
                        performing the given action.
        :param  environment:    the environment in which the action takes place.

        :returns  an ExpectedStateValue object.
        """
        assert isinstance(act, action.Action)
        assert isinstance(state, State)
        assert isinstance(environment, Environment)

        # TODO: sample a random amount of noise
        value = self.__func(act, state, environment)

        # compute the noise
        if self.__noise_func:
            noise = self.__noise_func(act, state, environment)
        else:
            noise = None

        return ExpectedStateValue(value, noise)


class FixedEstimator(Estimator):
    """
    A fixed estimator is one that always assigns a fixed value to its \
    associated state variable, rather than computing a value based on the \
    (action, state, environment) context.
    """

    def __init__(self, variable, value):
        super(FixedEstimator, self).__init__(variable, lambda act, state, env: value)
