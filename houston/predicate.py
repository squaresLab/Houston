class Predicate(object):
    """
    A predicate is used to check if a condition is met. It is used for preconditions,
    postconditions, and invariants.
    """

    def __init__(self,
                 name: str,
                 predicate):
        """
        Constructs a Predicate object that holds a name and a predicate
        """
        self.__name = name
        self.__predicate = predicate

    @property
    def name(self) -> str:
        """
        The name given to this predicate.
        """
        return self.__name

    def check(self,
              action: 'Action',
              current_state: 'State',
              env: 'Environment'):
        """
        Determines whether this predicate is satisfied by a given action, \
        state, and environment.

        :param  action              a description of the action being performed
        :param  current_state       a description of the state of the system
        :param  env                 a description of the environment

        :returns    True if satisified, false if not.
        """
        return self.__predicate(action, current_state, env)

    __call__ = check


class Invariant(Predicate):
    """
    Invariants are used to express statements about the system in formal logic
    that always remain true throughout the execution of an associated action.
    """
    pass


class Postcondition(Predicate):
    """
    Predicate that should be met after the execution of an action.
    """
    pass


class Precondition(Predicate):
    """
    Precondition that should be met before the execution of an action.
    """
    pass
