import pytest

from houston.command import Command, Parameter
from houston.valueRange import DiscreteValueRange
from houston.specification import Idle


def test_to_and_from_dict():
    class Boop(Command):
        uid = 'test:boop'
        name = 'boop'
        parameters = [
            Parameter('foo', DiscreteValueRange(['ON', 'OFF']))
        ]
        specifications = [Idle]

    x = Boop(foo='ON')
    d_expected = {
        'type': 'test:boop',
        'parameters': {
            'foo': 'ON'
        }
    }
    d_actual = x.to_dict()
    assert d_actual == d_expected

    y = Command.from_dict(d_actual)
    assert y.to_dict() == d_actual
