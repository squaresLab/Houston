class Predicate(object):
    """
    A predicate is used to check if a condition is met. It is used for preconditions,
    postconditions, and invariants.
    """

    def __init__(self, name, predicate):
        """
        Constructs a Predicate object that holds a name and a predicate
        """
        self.__name = name
        self.__predicate = predicate


    def check(self, action, currentState, env):
        """
        Determines whether this predicate is satisfied by a given action, \
        state, and environment.

        :param  action              a description of the action being performed
        :param  currentState        a description of the state of the system
        :param  env                 a description of the environment

        :returns    True if satisified, false if not.
        """
        return self.__predicate(action, currentState, env)


class Invariant(Predicate):
    """
    Invariants are used to express statements about the system in formal logic
    that always remain true throughout the execution of an associated action.
    """

    def __init__(self, name, description, predicate):
        """
        Constructs an Invariant object.

        :param  name            name of the invariant.
        :param  description     a short description of the invariant
        :param  predicate       lambda function that holds the condition to be met.
        """
        super(Invariant, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


    def getName(self):
        """
        Returns the name of this invariant
        """
        return self.__name


class Postcondition(Predicate):
    """
    Predicate that should be met after the execution of an action.
    """

    def __init__(self, name, description, predicate):
        """
        Constructs a Postcondition object.

        :param  name            name of the postcondition
        :param  description     a short description of the postcondition
        :param  predicate       lambda function that holds the condition to be met.
        """
        super(Postcondition, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


    def getName(self):
        """
        Returns the name of the Postcondition.
        """
        return self.__name


class Precondition(Predicate):
    """
    Precondition that should be met before the execution of an action.
    """

    def __init__(self, name, description, predicate):
        """
        Constructs a Precondition object

        :param  name                name of the precondition
        :param  description         a short description of the precondition
        :param  predicate           lambda function that holds the condition
                                    to be met.
        """
        super(Precondition, self).__init__(name, predicate)
        self.__name = name
        self.__description = description


    def getName(self):
        """
        Returns the name of the Precondition.
        """
        return self.__name


    def usesParameters(self):
        """
        Returns true if this precondition
        """
        return


    def getUsedParameters(self):
        pass


    def getUsedVariables(self):
        pass
