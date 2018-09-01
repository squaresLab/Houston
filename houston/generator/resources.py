# FIXME use attrs!
class ResourceUsage(object):
    """
    Used to monitor and record the resources used during a given
    test-generation trial.
    """
    @staticmethod
    def from_json(jsn):
        return ResourceUsage(jsn['num_missions'], jsn['running_time'])

    def __init__(self, num_missions=0, running_time=0.0):
        self.num_missions = num_missions
        self.running_time = running_time

    def to_json(self):
        return {'num_missions': self.num_missions,
                'running_time': self.running_time}


class ResourceLimits(object):
    """
    Used to specify limits on the resources that can be used during a given
    test-generation trial.
    """
    @staticmethod
    def from_json(jsn):
        return ResourceLimits(num_missions=jsn['num_missions'],
                              running_time=jsn['running_time'])

    def __init__(self, num_missions=None, running_time=None):
        self.__num_missions = num_missions
        self.__running_time = running_time

    def reached(self, usage):
        """
        Determines whether a given resource usage has reached the limits
        defined by this object.
        """
        if self.reached_mission_limit(usage.num_missions):
            return True
        if self.reached_time_limit(usage.running_time):
            return True
        return False

    @property
    def num_missions(self):
        """
        The maximum number of missions that may be generated, or None, if
        no such limit exists.
        """
        return self.__num_missions

    @property
    def running_time(self):
        """
        The maximum length of time that the test-generation process may take,
        or None, if there is no such limit.
        """
        return self.__running_time

    def reached_mission_limit(self, num_missions):
        """
        Determines whether a given number of missions exceeds the maximum
        number of missions that can be generated (as specified by this object).
        """
        return self.__num_missions is not None and \
            num_missions >= self.__num_missions

    def reached_time_limit(self, running_time):
        """
        Determines whether a given running time meets or exceeds the limit.
        """
        return self.__running_time is not None and \
            running_time >= self.__running_time

    def to_json(self):
        """
        Returns a JSON description of these limits.
        """
        return {'num_missions': self.__num_missions,
                'running_time': self.__running_time}
