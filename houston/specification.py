__all__ = ['Specification', 'Idle']

from typing import List, Iterator, Union, Callable
import random

import attr

from .state import State
from .environment import Environment
from .configuration import Configuration

Precondition = Callable[['Action', State, Environment, Configuration], bool]
Postcondition = \
    Callable[['Action', State, State, Environment, Configuration], bool]
Timeout = \
    Callable[['Action', State, Environment, Configuration], float]


@attr.s
class Specification(object):
    name = attr.ib(type=str)
    precondition = attr.ib(type=Precondition)
    postcondition = attr.ib(type=Postcondition)
    timeout = attr.ib(type=Timeout)


class Idle(Specification):
    def __init__(self, idle_time: float = 5.0) -> None:
        assert idle_time > 0

        def post(a, s0, s1, e, c) -> bool:
            time_passed = s1.time_offset - s0.time_offset
            reached_idle_time = time_passed > idle_time
            remained_same = s0.equiv(s1)
            return reached_idle_time and remained_same

        pre = lambda a, s, e, c: True
        timeout = lambda a, s, e, c: idle_time + 2.0
        super().__init__("idle", pre, post, timeout)
