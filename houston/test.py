import time
import docker

class TestSuite(object):
    """
    A test suite is an ordered set (i.e., a sequence with no repeated elements)
    of tests.
    """

    @staticmethod
    def fromFile(fn):
        """
        Constructs a test suite from a given file, containing a JSON-based
        description of its contents.

        :param  fn  the path to the test suite description file

        :returns    the corresponding TestSuite for that file
        """
        with open(fn, "r") as f:
            jsn = json.load(f)
        return TestSuite.fromJSON(jsn)


    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a test suite from its associated JSON description.
        """
        tests = [Mission.fromJSON(t) for t in jsn['tests']]
        return TestSuite(tests)


    def __init__(self, tests=[]):
        """
        Constructs a test suite.

        :param  tests   the (initial) contents of the test suite.
        """
        assert(isinstance(tests, list) and not tests is None)
        self.__contents = tests


    def execute(self, system):
        """
        Executes the tests contained within this suite.

        :param  system  the system-under-test

        :returns    A summary of the test suite execution, given as a
                    TestSuiteSummary object.
        """
        startTime = time.time()

        # TODO for now, we execute tests sequentially
        outcomes = []
        for test in self.__contents:
            outcome = self.executeTest(test, system)

        # measure the wall clock running-time
        endTime = time.time()
        runningTime = endTime - startTime

        # return a summary
        summary = TestSuiteSummary(runningTime)
        return summary


    def executeTest(self, system, test):

        # launch container
        # systemContainer = system.launchContainer()
        client = docker.from_env()

        try:

            # wait until server is running
            while True:
                time.sleep(0.1)
                # is the server ready?

            # communicate with server

            return MissionOutcome()
        
        finally:
            container.stop()


    def toJSON(self):
        """
        Returns a JSON-based description of this test suite.
        """
        return [t.toJSON() for t in self.__contents]


    def toFile(self, fn):
        """
        Saves the contents of this test suite to a file on disk.

        :param  fn  the path to the file.
        """
        jsn = self.toJSON()
        with open(fn, "w") as f:
            json.dump(jsn, f)


class MissionSuiteCharacteristics(object):
    """
    Used to describe the desired characteristics of a mission suite.
    """
    def __init__(self, maxNumMissions, maxNumActionsPerMission, maxTime):
        """
        Constructs a set of desired mission suite characteristics

        :param  maxNumMissions: the maximum number of missions that should be\
                                contained within the suite.
        :param  maxNumActionsPerMission: the maximum number of actions that\
                                each mission can contain.
        :param  maxTime: the maximum running time of the entire mission suite.
        """
        self.__maxMissions           = maxMissions
        self.__maxActionsPerMission  = maxActionsPerMission
        self.__maxTime               = maxTime


    def getMaxNumMissions(self):
        return self.__maxMissions


    def getMaxNumActionsPerMission(self):
        return self.__maxActions


    def getMaxTime(self):
        """
        Returns the desired maximum running time of the test suite.

        TODO: a desired `maximum' doesn't entirely make sense?
        """
        return self.__maxTime



class MissionSuiteSummary(object):
    """
    Contains a summary of the execution of a mission suite.
    """

    def __init__(self, wallTime):
        assert(isinstance(wallTime, float) and not wallTime is None)
        self.__wallTime = wallTime
        self.__outcomes = []


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


    def toJSON(jsn):
        """
        Returns a serialised form of this summary as a JSON-ready dictionary.
        """
        raise NotImplementedError
