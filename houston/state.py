import copy

class State(object):
    """
    Describes the state of the system at a given moment in time, in terms of
    its internal and external variables.
    """

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
    Estimates the expected state after the execution of an action.
    """
    def __init__(self, variable, func):
        """
        Constructs an estimator for a given state variable.

        :param   variable       stateVariable to be estimated
        :param   func           lambda function that holds the operation to
                                calculate the expected state after the execution
                                of an action.
        """
        self.__variable = variable
        self.__func     = func

    def getVariableName(self):
        """
        Returns the name of the systemVariable
        """
        return self.__variable

    def estimate(self, action, state, environment):
        """
        Returns the expected value for the stateVariable.

        :param    action        action used to calculate the expected state.
        :param    state         current state of the system.
        :param    environment   current environment of the system.
        """
        return self.__func(action.getParameters(), state, environment)
