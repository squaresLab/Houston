class ValueRange(object):
    """
    Used to represent a range of possible values for a variable, parameter,
    or setting.
    """

    def sample(self):
        """
        Returns a 
        """
        raise NotImplementedError


class DiscreteValueRange(ValueRange):

    def __init__(self, values):
        assert(values is not None)
        assert(isinstance(values, list) or isinstance(values, range))

        self.__values = values
        if isinstance(values, range):
            self.__typ = int
            if values.step() > 0:
                self.__size = (values.stop() - values.start()) / values.step()
            else:
                self.__size = (values.start() - values.stop()) / values.step()

        else:
            self.__size = len(values)
            assert(self.__size > 0)
            self.__typ = type(values[0])
            assert(all(type(v) == self.__typ for v in values))

    
    def size(self):
        """
        Returns the number of values within this range.
        """
        return self.__size

    
    def sample(self):
        raise NotImplementedError


class ContinuousValueRange(ValueRange):

    def __init__(self, min_value, max_value, inclusive):
        self.__min_value = min_value
        self.__max_value = max_value
        self.__inclusive = inclusive


    def sample(self):
        raise NotImplementedError
