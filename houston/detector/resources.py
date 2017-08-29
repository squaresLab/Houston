class ResourceUsage(object):
    """
    Used to monitor and record the resources used during a given
    test-generation trial.
    """
    @staticmethod
    def fromJSON(jsn):
        return ResourceUsage(jsn['numMissions'], jsn['runningTime'])


    """
    Simple data structure used to maintain track of what resources have been
    consumed over the course of a bug detection trial.
    """
    def __init__(self, numMissions = 0, runningTime = 0.0):
        self.numMissions = numMissions
        self.runningTime = runningTime


    def toJSON(self):
        return {
            'numMissions': self.numMissions,
            'runningTime': self.runningTime
        }


class ResourceLimits(object):
    """
    Used to specify limits on the resources that can be used during a given
    test-generation trial.
    """
    @staticmethod
    def fromJSON(jsn):
        return ResourceLimits(numMissions =  jsn['numMissions'], runningTime = jsn['runningTime'])


    def __init__(self, numMissions = None, runningTime = None):
        self.__numMissions = numMissions
        self.__runningTime = runningTime


    def reached(self, usage):
        if self.reachedMissionLimit(usage.numMissions):
            return True
        if self.reachedTimeLimit(usage.runningTime):
            return True
        return False


    def getNumMissions(self):
        return self.__numMissions


    def reachedMissionLimit(self, numMissions):
        return  self.__numMissions is not None and \
                    numMissions >= self.__numMissions


    def reachedTimeLimit(self, runningTime):
        """
        Determines whether a given running time meets or exceeds the limit.

        :param  runningTime:    the length of time that the trial has been
                                running, measured in wall-clock seconds.

        :returns    True if the time limit has been reached, else False.
        """
        return  self.__runningTime is not None and \
                    runningTime >= self.__runningTime


    def toJSON(self):
        """
        Returns a JSON description of these limits.
        """
        return {
            'numMissions': self.__numMissions,
            'runningTime': self.__runningTime
        }
