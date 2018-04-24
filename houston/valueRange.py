import random

class ValueRange(object):
    """
    Used to represent a range of possible values for a variable, parameter,
    or setting.
    """

    def sample(self):
        """
        Uses uniform selection to sample a single value from this range.
        """
        raise NotImplementedError


    @property
    def type(self):
        """
        The type of values within this range.
        """
        raise NotImplementedError


class DiscreteValueRange(ValueRange):
    """
    Covers both discrete numbers and enumerations.
    """

    def __init__(self, values):
        assert (isinstance(values, list) or isinstance(values, type(range)))
        self.__values = values
        if isinstance(values, type(range)):
            self.__typ = int
            if values.step() > 0:
                self.__size = (values.stop() - values.start()) / values.step()
            else:
                self.__size = (values.start() - values.stop()) / values.step()

        else:
            self.__size = len(values)
            assert (self.__size > 0)
            self.__typ = type(values[0])
            assert all(type(v) == self.__typ for v in values)


    def __str__(self):
        return str(self.__values)


    @property
    def size(self):
        """
        Returns the number of values within this range.
        """
        return self.__size


    def sample(self, rng):
        assert (isinstance(rng, random.Random) and rng is not None)
        return rng.choice(self.__values)


    @property
    def type(self):
        return self.__typ


class ContinuousValueRange(ValueRange):

    def __init__(self, min_value, max_value, inclusive=False):
        """
        Constructs a continuous value range.

        :param  min_value:  the minimum value within the range
        :param  max_value:  the maximum value within the range
        :param  inclusive:  a flag indicating whether the range should be\
                            half-open or full-open.
        """
        assert isinstance(min_value, float)
        assert isinstance(max_value, float)
        assert isinstance(inclusive, bool)

        self.__min_value = min_value
        self.__max_value = max_value
        self.__inclusive = inclusive


    def sample(self, rng):
        assert isinstance(rng, random.Random)
        return rng.uniform(self.__min_value, self.__max_value)

    
    @property
    def type(self):
        return float
