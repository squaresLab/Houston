import random

class MissionGenerator(object):

    def __init__(self, threads, max_num_actions):
        assert isinstance(threads, int)
        assert isinstance(max_num_actions, int)
        assert threads > 0
        assert max_num_actions > 0

        self.__rng = None
        self.__threads = threads
        self.__max_num_actions = max_num_actions
        self.__resource_limits = None
        self.__resource_usage = None
        self.__start_time = None

    
    @property
    def max_num_actions(self):
        """
        The maximum number of actions that may be present in a mission
        produced by this generator.
        """
        return self.__max_num_actions


    @property
    def threads(self):
        """
        The number of threads available to this generator.
        """
        return self.__threads


    @property
    def rng(self):
        """
        Returns the pseudorandom number generator used by this generator.
        """
        return self.__rng


    def tick(self):
        """
        Used to measure the running time of the current generation trial.
        """
        self.__resource_usage.running_time = \
            timeit.default_timer() - self.__start_time


    def generate(self, system, image, seed, resource_limits):
        assert isinstance(seed, int)
        assert isinstance(image, str)

        self.prepare(system, image, seed, resource_limits)

        self.__start_time = timeit.default_timer()


    def prepare(self, system, image, seed, resource_limits):
        """
        Prepares the state of this generator immediately before beginning a
        new generation trial.
        """
        self.__system = system
        self.__image = image
        self.__resource_limits = resource_limits
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self.__rng = random.Random(seed)

    
    def exhausted(self):
        """
        Checks whether the resources available to this generator have been
        exhausted.
        """
        return self.__resource_limits.reached(self.__resource_usage)


    def generate_mission(self):
        """
        Generates a single mission according to the generation strategy defined
        by this generator.
        """
        raise NotImplementedError


    def next(self):
        pass


class RandomMissionGenerator(object):
