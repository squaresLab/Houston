class ResourceUsage(object):
    """
    Used to monitor and record the resources used during a given
    test-generation trial.
    """
    @staticmethod
    def from_json(jsn):
        return ResourceUsage(jsn['numMissions'], jsn['runningTime'])


    """
    Simple data structure used to maintain track of what resources have been
    consumed over the course of a bug detection trial.
    """
    def __init__(self, num_missions = 0, running_time = 0.0):
        self.num_missions = num_missions
        self.running_time = running_time


    def toJSON(self):
        return {
            'numMissions': self.num_missions,
            'runningTime': self.running_time
        }


class ResourceLimits(object):
    """
    Used to specify limits on the resources that can be used during a given
    test-generation trial.
    """
    @staticmethod
    def from_json(jsn):
        return ResourceLimits(num_missions =  jsn['numMissions'],
                              running_time = jsn['runningTime'])


    def __init__(self, num_missions = None, running_time = None):
        self.__num_missions = num_missions
        self.__running_time = running_time


    def reached(self, usage):
        if self.reached_mission_limit(usage.num_missions):
            return True
        if self.reached_time_limit(usage.running_time):
            return True
        return False


    @property
    def num_missions(self):
        return self.__num_missions


    def reached_mission_limit(self, num_missions):
        return  self.__num_missions is not None and \
                    num_missions >= self.__num_missions


    def reached_time_limit(self, running_time):
        """
        Determines whether a given running time meets or exceeds the limit.

        :param  running_time:    the length of time that the trial has been
                                running, measured in wall-clock seconds.

        :returns    True if the time limit has been reached, else False.
        """
        return  self.__running_time is not None and \
                    running_time >= self.__running_time


    def to_json(self):
        """
        Returns a JSON description of these limits.
        """
        return {
            'numMissions': self.__num_missions,
            'runningTime': self.__running_time
        }
