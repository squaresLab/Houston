from typing import TypeVar, Generic, List, Callable

__all__ = ['Message', 'Connection']


class Message(object):
    """
    Base class used all messages.
    """


T = TypeVar('T')
@attr.s
class Connection(Generic[T]):
    def __init__(self, hooks: List[Callable[T], None]) -> None:
        self.__trace = []  # type: List[T]
        self.__hooks = hooks if hooks else []

    def receive(self, message: T) -> None:
        # TODO store trace?
        for hook in self.__hooks:
            hook(message)

    def send(self, message: T) -> None:
        """
        Attempts to send a given message to the system under test.
        """
        raise NotImplementedError
