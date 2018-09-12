import pytest

from houston.action import Action
from houston.state import State, Environment, var
from houston.predicate import Postcondition, Precondition, Invariant


def test_postcondition():
    class S(State):
        x = var(int, lambda c: 0)
        y = var(int, lambda c: 0)

    action = Action('goto', {'x': 10, 'y': 5})
    state_before = S(x=3, y=0, time_offset=0.0)
    state_after = S(x=10, y=5, time_offset=1.0)
    env = Environment({})

    p = Postcondition("position: x",
                      lambda action, state, env: state_after.x == action['x'])
    p = Postcondition("position: y",
                      lambda action, state, env: state_after.y == action['y'])
