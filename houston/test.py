class Test(object):
    """
    Describe difference between missions and tests.
    """
    

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a given test from a JSON description.
        """


    def __init__(self, mission, context):
        self.__mission = mission
        self.__context = context

    
    def toJSON(self):
        """
        Returns a JSON description (in the form of a dictionary) of this test.
        """
        return {
            'mission': self.__mission.toJSON()
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
            jsn = json.load(fn)
        return TestSuite.fromJSON(jsn)


    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a test suite from its associated JSON description.
        """
        pass


class TestSuiteSummary(object):
    """
    Contains a summary of the execution of a test suite.
    """


    def __init__(self):
        self.__wallTime = 0.0


    def getWallClockTime(self):
        """
        Returns the wall-clock running time taken to execute the test suite,
        measured in seconds.
        """
        return self.__wallTime
