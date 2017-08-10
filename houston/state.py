import copy
import json

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


    def isExpected(self, observed):
        if self.__noise is None:
            return self.__value == observed
        else:
            return (self.__value - self.__noise) < observed <(self.__value + self.__noise)


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


    def isExpected(self, st):
        for name, expectedValue in self.__values.items():
            if not expectedValue.isExpected(st.read(name)):
                return False

        return True


class StateVariable(object):

    def __init__(self, name, getter):
        """
        Constructs a new state variable

        :param  name:   the name of this variable
        :param  type:   the type of this variable
        :param  getter: a lambda function, used to obtain the value of this variable
        """
        assert(isinstance(self, InternalVariable) or isinstance(self, ExternalVariable))
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


    def computeExpectedValue(self, action, state, environment):
        """
        Computes the expected value for the variable associated with this estimator,
        within a given state and environment.

        :param    action        action used to calculate the expected state.
        :param    state         the state of the system immediately prior to
                                performing the given action.
        :param    environment   the environment in which the action takes place.

        :returns  an ExpectedStateValue object.
        """
        # TODO: sample a random amount of noise
        value = self.__func(action, state, environment)
        noise = None
        if self.__noiseFunc:
            noise = self.__noiseFunc(action, state, environment)
        return ExpectedStateValue(value, noise)


class FixedEstimator(Estimator):
    """
    A fixed estimator is one that always assigns a fixed value to its \
    associated state variable, rather than computing a value based on the \
    (action, state, environment) context.
    """

    def __init__(self, variable, value):
        super(FixedEstimator, self).__init__(variable, lambda action, state, env: value)
