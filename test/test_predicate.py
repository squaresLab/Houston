from houston.action import Action
from houston.state import State, Environment
from houston.predicate import Postcondition, Precondition, Invariant


def test_postcondition():
    action = Action('goto', {'x': 10, 'y': 5})
    state_before = State({'x': 3, 'y': 0}, 0.0)
    state_after = State({'x': 10, 'y': 5}, 1.0)
    env = Environment({})

    p = Postcondition("position: x",
                      lambda action, state, env: state_after['x'] == action['x'])
    p = Postcondition("position: y",
                      lambda action, state, env: state_after['y'] == action['y'])
