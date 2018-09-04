__all__ = ['Predicate']

from typing import Callable

import attr


@attr.s(frozen=True)
class Predicate(object):
    """
    A predicate is used to check if a condition is met. Predicates are used
    to implement preconditions, postconditions, and invariants for a variety
    of purposes.
    """
    name = attr.ib(type=str)
    predicate = attr.ib(type=Callable[['Action', 'State', 'Environment'],
                                      bool])

    def check(self,
              action: 'Action',
              state: 'State',
              environment: 'Environment'
              ) -> bool:
        """
        Determines whether this predicate is satisfied by a given action,
        state, and environment.

        Parameters:
            action: details of the command being executed.
            state: the state of the system.
            environment: the state of the environment.

        Returns:
            True if this predicate is satisfied by the given information.
        """
        return self.predicate(action, state, environment)

    __call__ = check


class Invariant(Predicate):
    """
    Invariants are used to express statements about the system in formal logic
    that always remain true throughout the execution of an associated action.
    """


class Postcondition(Predicate):
    """
    Predicate that should be met after the execution of an action.
    """


class Precondition(Predicate):
    """
    Precondition that should be met before the execution of an action.
    """
