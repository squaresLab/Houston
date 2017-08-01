"""
The generator module is responsible for providing a number of different test
suite generation approaches.

- maximise code coverage
- maximise (behavioural) diversity
- maximise mutant score
- minimise expected time to cause failure (obtained via use of mutants)

"""

class TestSuiteGenerator(object):
    """
    TestSuiteGenerator defines a common interface for all test suite
    generation approaches.
    """


    def __init__(self, system):
        """
        Constructs a test suite generator for a given system.
        """
        self.__system = system


    def getSystem(self):
        """
        Returns a description of the system for which this generator should
        generate test suites.
        """
        return self.__system


    def generate(self, characteristics, limits):
        """
        Using no more than a specified set of resources, this method generates
        a set of missions that satisfy given characteristics using the strategy
        associated with this generator.

        :param  characteristics A description of the desired characteristics of the
                                resulting test suite.
        :param  limits          A description of the limited resources
                                available for the purposes of generating the
                                test suite.

        :return A TestSuite object.
        """

        # ResourceUsage and ResourceLimit objects
        raise NotImplementedError


class RandomGenerator(TestSuiteGenerator):
    """
    The random generator iteratively constructs a test suite (at random,
    without any direction) until the resulting suite satisfies the
    characteristics specified by the user (e.g., number of tests, expected
    running time).

    What if the generator fails to generate such a set within the given time
    limits? Should it return the current state of its set, or should it just
    throw an exception?
    """


    def generate(self, characteristics, limits):
        assert(isinstance(characteristics, TestSuiteCharacteristics))
        assert(not characteristics is None)

        tests = TestSuite()

        while not tests.satisfies(characteristics):
            m = self.__generate_mission()
            tests.add(m)

        return tests 


    def __generate_mission(self):
        """
        Generates a single test at random.

        :returns    A randomly-generated Test instance
        """

        # generate a mission context

        # generate a mission
        
        raise NotImplementedError


class DirectedGenerator(TestSuiteGenerator):
    pass
