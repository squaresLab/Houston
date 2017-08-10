import time
import docker
import json
import houston
from pprint import pprint as pp

class MissionSuite(object):
    """
    A mission suite is an ordered set (i.e., a sequence with no repeated elements)
    of missions.
    """

    @staticmethod
    def fromFile(fn):
        """
        Constructs a mission suite from a given file, containing a JSON-based
        description of its contents.

        :param  fn  the path to the mission suite description file

        :returns    the corresponding MissionSuite for that file
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        return MissionSuite.fromJSON(jsn)

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a mission suite from its associated JSON description.
        """
        missions = [houston.mission.Mission.fromJSON(t) for t in jsn['missions']]
        return MissionSuite(missions)

    def __init__(self, missions=[]):
        """
        Constructs a mission suite.

        :param  missions    the (initial) contents of the mission suite.
        """
        assert (isinstance(missions, list) and not missions is None)
        self.__contents = missions

    def add(self, mission):
        """
        Appends a mission to contents

        :param  mission     mission to append
        """
        self.__contents.append(mission)

    def satisfiesMissionNumber(self, characteristics):
        """
        Checks if the state of the mission suite satisfies the characteristics given.

        :param    characteristics       MissionSuiteCharacteristics
        """
        if len(self.__contents) < characteristics.getMaxNumMissions():
            return False
        #TODO How to check expected running time?
        return True


    def execute(self, systm, image):
        """
        Executes the tests contained within this suite.

        :param  system  the system-under-test

        :returns    A summary of the test suite execution, given as a
                    TestSuiteSummary object.
        """
        startTime = time.time()

        # TODO for now, we execute tests sequentially
        outcomes = []
        for tst in self.__contents:
            outcomes.append(self.executeMission(systm, image, tst))
        # measure the wall clock running-time
        endTime = time.time()
        runningTime = endTime - startTime

        # return a summary
        summary = MissionSuiteSummary(runningTime, outcomes)
        return summary


    def executeMission(self, systm, image, mission):
        cntr = houston.createContainer(systm, image)
        try:
            while not cntr.ready():
                time.sleep(0.1)

            return cntr.execute(mission)

        finally:
            houston.destroyContainer(cntr)


    def toJSON(self):
        """
        Returns a JSON-based description of this test suite.
        """
        return {'missions': [t.toJSON() for t in self.__contents]}


    def toFile(self, fn):
        """
        Saves the contents of this test suite to a file on disk.

        :param  fn  the path to the file.
        """
        jsn = self.toJSON()
        with open(fn, "w") as f:
            json.dump(jsn, f,sort_keys=True, indent=4)


class MissionSuiteCharacteristics(object):
    """
    Used to describe the desired characteristics of a mission suite.
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a mission suite characteristics from its associated JSON
        description.
        """
        assert (isinstance(jsn, dict))
        assert ('suite' in jsn)
        assert ('mission' in jsn)
        assert ('action' in jsn)
        assert ('maxTime' in jsn['suite'])
        assert ('maxMissions' in jsn['suite'])

        ac = ActionCharacteristics.fromJSON(jsn['actions'])
        mc = MissionCharacteristics.fromJSON(jsn['missions'])
        maxTime = jsn['suite']['maxTime']
        maxMissions = jsn['suite']['maxMissions']

        return MissionSuiteCharacteristics(maxTime, maxMissions, mc, ac)


    def __init__(self, maxTime, maxMissions, aCharacteristics, mCharacteristics):
        """
        Constructs a set of desired mission suite characteristics

        :param  maxTime: the maximum running time of the entire mission suite.

        :param  maxMissions: the maximum number of missions that should be\
                                contained within the suite.

        """
        self.__maxTime = maxTime
        self.__maxMissions = maxMissions


    def getMaxTime(self):
        """
        Returns the maximum duration of a mission suite.
        """
        return self.__maxTime


    def getMaxMissions(self):
        """
        Returns the maximum number of missions per mission suite.
        """
        return self.__maxMissions


class MissionCharacteristics(object):
    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a mission suite characteristics from its associated JSON
        description.
        """
        assert (isinstance(jsn, dict))
        assert ('maxTime' in jsn)
        assert ('maxActions' in jsn)
        return MissionCharacteristics(jsn['maxTime'], jsn['maxActions'])


    def __init__(self, maxTime, maxActions):
        """
        Constructs a set of desired mission suite characteristics

        :param  maxTime: the maximum running time of a mission.

        :param  maxActions: the maximum number of actions that\
                                each a mission can contain.

        """
        self.__maxTime = maxTime
        self.__maxActions = maxActions


    def getMaxTime(self):
        """
        Returns the maximum duration of a mission.
        """
        return self.__maxTime


    def getMaxActions(self):
        """
        Returns the maximum number of actions per mission.
        """
        return self.maxActions


class ActionCharacteristics(object):
    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an action characteristics from its associated JSON
        description.
        """
        assert (isinstance(jsn, dict))
        assert ('maxTime' in jsn)
        return ActionCharacteristics(jsn['maxTime'])


    def __init__(self, maxTime):
        """
        Constructs a set of desired action characteristics.

        :param  maxTime: the maximum duration of an action.
        """
        self.__maxTime = maxTime


    def getMaxTime(self):
        """
        Returns the maximum duration of an action.
        """
        return self.__maxTime


class GeneratorResourceLimits(object):
    """
    Used to describe the limits that the generator has when generating a mission
    suite.
    """
    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a mission suite limits  from its associated JSON
        description.
        """
        assert (isinstance(jsn, dict))
        assert ('maxTime' in jsn)
        assert ('maxNumRetries' in jsn)
        return GeneratorResourceLimits(jsn['maxTime'], jsn['maxNumRetries'])

    def __init__(self, maxTime, maxNumRetries):
        """
        Constructs a set of limitations for the missionSuiteGenerator.

        :param  maxTime:       the maximum time that the generator can take to
                               generate a mission suite
        :param  maxNumRetries  the maximum number of tries that the generator
                               has to come up with a valid action
        """
        self.__maxTime = maxTime
        self.__maxNumRetries = maxNumRetries

    def getMaxTime(self):
        """
        Returns the maximum time that the generator can take to generate a mission
        suite.
        """
        return self.__maxTime

    def getMaxNumRetries(self):
        """
        Returns the maximum number of tries that the generator has to come up
        with a valid action.
        """
        return self.__maxNumRetries


class MissionSuiteSummary(object):
    """
    Contains a summary of the execution of a mission suite.
    """
    @staticmethod
    def fromJSON(self, jsn):
        """
        Constructs a mission suite summary from a given dict, containing a
        JSON-based description of its contents.
        """
        assert (isinstance(jsn, dict))
        assert ('wallTime' in jsn)
        assert ('outcomes' in jsn)
        return MissionSuiteSummary(jsn['wallTime'], jsn['outcomes'])

    def __init__(self, wallTime, outcomes):
        assert (isinstance(wallTime, float) and not wallTime is None)
        self.__wallTime = wallTime
        self.__outcomes = outcomes


    def hasFailures(self):
        """
        Determines whether any missions within the suite failed.
        """
        raise NotImplementedError


    def getWallClockTime(self):
        """
        Returns the wall-clock running time taken to execute the mission suite,
        measured in seconds.
        """
        return self.__wallTime


    def toJSON(self):
        """
        Returns a serialised form of this summary as a JSON-ready dictionary.
        """
        return {
            "wallTime": self.__wallTime,
            "outcomes": [outcome.toJSON() for outcome in self.__outcomes]
        }
