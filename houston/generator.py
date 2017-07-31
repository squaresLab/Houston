"""
The generator module is responsible for providing a number of different test
suite generation approaches.

- maximise code coverage
- maximise (behavioural) diversity
- maximise mutant score
- minimise expected time to cause failure (obtained via use of mutants)

"""

class MissionSetGenerator(object):
    """
    MissionSetGenerator defines a common interface for all mission set
    generation approaches.
    """


    def __init__(self, system):
        """
        Constructs a mission set generator for a given system.
        """
        self.__system = system


    def getSystem(self):
        """
        Returns a description of the system for which this generator should
        generate set(s) of missions.
        """
        return self.__system


    def generate(self, characteristics, limits):
        """
        Using no more than a specified set of resources, this method generates
        a set of missions that satisfy given characteristics using the strategy
        associated with this generator.

        :param  characteristics A description of the desired characteristics of the
                                resulting mission set.
        :param  limits          A description of the limited resources
                                available for the purposes of generating a set
                                of missions.

        :return A set of Mission objects
        """

        # ResourceUsage and ResourceLimit objects
        raise NotImplementedError


class RandomGenerator(MissionSetGenerator):
    """
    The random generator iteratively constructs a set of missions (at random,
    without any direction) until the resulting set satisfies the
    characteristics specified by the user (e.g., number of missions, expected
    running time of mission set).

    What if the generator fails to generate such a set within the given time
    limits? Should it return the current state of its set, or should it just
    throw an exception?
    """


    def generate(self, characteristics, limits):
        missions = MissionSet()

        while not missions.satisfies(characteristics):
            m = self.__generate_one()
            missions.add(m)

        return missions


    def __generate_one(self):
        """
        Generates a single mission at random.

        :returns    A randomly-generated Mission instance
        """
        raise NotImplementedError


class DirectedGenerator(MissionSetGenerator):
    pass
