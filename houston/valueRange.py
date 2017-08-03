class ValueRange(object):
    """
    Used to represent a range of possible values for a variable, parameter,
    or setting.
    """
    pass

    def sample(self):
        """
        Returns a 
        """
        raise NotImplementedError


class DiscreteValueRange(ValueRange):
    pass


class ContinuousValueRange(ValueRange):
    pass
