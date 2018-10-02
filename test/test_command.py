import pytest
import attr

from houston.connection import Message
from houston.command import Command, Parameter
from houston.valueRange import DiscreteValueRange
from houston.specification import Idle


def test_eq():
    @attr.s(frozen=True)
    class M1(Message):
        foo = attr.ib(type=str)

    class C1(Command):
        name = 'c1'
        parameters = [
            Parameter('foo', DiscreteValueRange(['ON', 'OFF']))
        ]
        specifications = [Idle]

        def to_message(self):
            return M1(self.foo)

    x = C1(foo='ON')
    y = C1(foo='OFF')
    a = C1(foo='ON')
    b = C1(foo='OFF')

    assert x == x
    assert y == y
    assert x != y
    assert y != x
    assert a != b
    assert b != a
    assert x == a
    assert y == b


def test_to_and_from_dict():
    @attr.s(frozen=True)
    class M1(Message):
        foo = attr.ib(type=str)

    class Boop(Command):
        uid = 'test:boop'
        name = 'boop'
        parameters = [
            Parameter('foo', DiscreteValueRange(['ON', 'OFF']))
        ]
        specifications = [Idle]

        def to_message(self):
            return M1(self.foo)

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