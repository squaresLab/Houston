import copy
import json
import action

class State(object):
    """
    Describes the state of the system at a given moment in time, in terms of
    its internal and external variables.
    """
    @staticmethod
    def fromFile(fn):
        """
        Constructs a system state from a given file, containing a JSON-based
        description of its contents.

        :param  fn  the path to the state description file

        :returns    the corresponding State for that file
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        print jsn.keys()
        return State.fromJSON(jsn)

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a description of a state from its JSON description.
        """
        assert ('variables' in jsn)
        assert (isinstance(jsn['variables'], dict))
        return State(jsn['variables'])


    def __init__(self, values):
        """
        Constructs a description of the system state.

        :param  values: a dictionary describing the values of the state
                        variables, indexed by their names.
        """
        self.__values = copy.copy(values)


    def getValues(self):
        """
        Returns the values of each of the state variables as a dictionary,
        indexed by name.
        """
        return copy.copy(self.__values)


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
            print('Variable: {} - State: {}'.format(variable, self.read(variable)))


    def toJSON(self):
        """
        Returns a JSON description of this state.
        """
        return {
            'variables': copy.copy(self.__values)
        }


    def __str__(self):
        return str(self.toJSON())


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


    def isExpected(self, observed, measurementNoise):
        assert (observed is not None)
        assert (measurementNoise is None or type(measurementNoise) == type(observed))

        # add the measurement noise to the action noise
        if measurementNoise is None:
            noise = self.__noise
        elif self.__noise is not None:
            noise = self.__noise + measurementNoise
        else:
            noise = measurementNoise

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
        for (name, val) in to.getValues().items():
            expected[name] = ExpectedStateValue(val)
        return ExpectedState(expected)


    def __init__(self, values):
        """
        Constructs a description of an expected state of the system.
        """
        assert (isinstance(values, dict))
        self.__values = values


    def isExpected(self, variables, st):
        """
        :param  variables:      a dictionary containing the definitions of \
                                the variables for the system under test, \
                                indexed by their names
        :param  st:             the observed state of the system

        :returns    True if the observed state of the system was expected
        """
        assert (isinstance(variables, dict) and dict is not None)
        assert (all(isinstance(k, str) for k in variables))
        assert (all(isinstance(v, StateVariable) for v in variables.values()))
        assert (isinstance(st, State) and st is not None)

        for (name, expectedValue) in self.__values.items():
            measurementNoise = variables[name].getNoise()
            if not expectedValue.isExpected(st.read(name), measurementNoise):
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
    def isNoisy(self):
        return self.__noise is not None


    """
    Returns the inherent level of noise that is to be expected when measuring
    this variable. If no noise is expected, None is returned.
    """
    def getNoise(self):
        return self.__noise


    """
    Returns the name of this system variable
    """
    def getName(self):
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
        return Environment.fromJSON(jsn)

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a description of an environment from its JSON description.
        """
        assert ('constants' in jsn)
        assert (isinstance(jsn['constants'], dict))
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


    def read(self, variable):
        """
        Returns the value of a given environment constant.
        """
        return self.__values[variable]


    def toJSON(self):
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

    def __init__(self, variable, func, noiseFunc = None):
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
        assert (isinstance(variable, str) and not variable is None)
        assert (callable(func))
        assert (callable(noiseFunc) or noiseFunc is None)

        self.__variable = variable
        self.__func = func
        self.__noiseFunc = noiseFunc


    def getVariableName(self):
        """
        Returns the name of the variable that is being estimated.
        """
        return self.__variable


    def computeExpectedValue(self, act, state, environment):
        """
        Computes the expected value for the variable associated with this estimator,
        within a given state and environment.

        :param  act:    action used to calculate the expected state.
        :param  state:  the state of the system immediately prior to \
                        performing the given action.
        :param  environment:    the environment in which the action takes place.

        :returns  an ExpectedStateValue object.
        """
        assert (isinstance(act, action.Action) and action is not None)
        assert (isinstance(state, State) and state is not None)
        assert (isinstance(environment, Environment) and environment is not None)

        # TODO: sample a random amount of noise
        value = self.__func(act, state, environment)

        # compute the noise
        if self.__noiseFunc:
            noise = self.__noiseFunc(act, state, environment)
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
