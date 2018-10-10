__all__ = ['Message', 'Connection']

from typing import Generic, TypeVar, List, Callable

T = TypeVar('T')


class Message(object):
    """
    Base class used by all messages.
    """


class Connection(Generic[T]):
    """
    Provides a connection to the system under test using a given protocol.
    """
    def __init__(self, hooks: List[Callable[[T], None]]) -> None:
        """
        Establishes a new connection.

        Parameters:
            hooks: A list of callables that should be called upon receiving
                a message via this connection.
        """
        self.__hooks = hooks if hooks else []

    def receive(self, message: T) -> None:
        """
        Forwards any received messages using the hooks attached to this
        connection.
        """
        for hook in self.__hooks:
            hook(message)

    def send(self, message: T) -> None:
        """
        Attempts to send a given message to the system under test.
        """
        raise NotImplementedError

    def close(self) -> None:
        """
        Closes the connection if open.
        """
        raise NotImplementedError

    def add_hooks(self, hooks: List[Callable[[T], None]]) -> None:
        self.__hooks.extend(hooks)
