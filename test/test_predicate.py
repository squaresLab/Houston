import pytest

from houston.command import Command
from houston.state import State, var
from houston.environment import Environment
from houston.predicate import Postcondition, Precondition, Invariant


def test_postcondition():
    class S(State):
        x = var(int, lambda c: 0)
        y = var(int, lambda c: 0)

    cmd = Command('goto', {'x': 10, 'y': 5})
    state_before = S(x=3, y=0, time_offset=0.0)
    state_after = S(x=10, y=5, time_offset=1.0)
    env = Environment({})
