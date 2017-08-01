import time

class Test(object):
    """
    Tests are comprised of a mission, and a context (i.e., the state of the
    environment, and the internal and external variables) in which the mission
    should be executed.
    """


    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a given test from a JSON description.
        """
        mission = Mission.fromJSON(jsn['mission'])
        context = MissionContext.fromJSON(jsn['context'])
        return Test(mission, context)


    def __init__(self, mission, context):
        assert(isinstance(mission, Mission) and not mission is None)
        assert(isinstance(context, MissionContext) and not context is None)
        self.__mission = mission
        self.__context = context


    def execute(self, system):
        """
        Executes this test.

        :param  system  A description of the system-under-test (SUT)

        :returns    a summary of the test, in the form of a TestOutcome object
        """
        raise NotImplementedError


    def toJSON(self):
        """
        Returns a JSON description (in the form of a dictionary) of this test.
        """
        return {
            'mission': self.__mission.toJSON(),
            'context': self.__context.toJSON()
        }


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
        tests = [Test.fromJSON(t) for t in jsn['tests']]
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
            outcome = test.execute(system)

        # measure the wall clock running-time
        endTime = time.time()
        runningTime = endTime - startTime

        # return a summary
        summary = TestSuiteSummary(runningTime)
        return summary


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


class TestSuiteCharacteristics(object):
    """
    Used to describe the desired characteristics of a test suite.
    """
    pass


class TestSuiteSummary(object):
    """
    Contains a summary of the execution of a test suite.
    """

    def __init__(self, wallTime):
        assert(isinstance(wallTime, float) and not wallTime is None)
        self.__wallTime = wallTime
        self.__outcomes = []


    def hasFailures(self):
        """
        Determines whether any tests within the suite failed.
        """
        raise NotImplementedError


    def getWallClockTime(self):
        """
        Returns the wall-clock running time taken to execute the test suite,
        measured in seconds.
        """
        return self.__wallTime


    def toJSON(jsn):
        """
        Returns a serialised form of this summary as a JSON-ready dictionary.
        """
        raise NotImplementedError
