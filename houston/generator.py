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

        pass


class RandomGenerator(MissionSetGenerator):


    def generate(self, limits):
        missions = set()
        return missions


class DirectedGenerator(MissionSetGenerator):
    pass
