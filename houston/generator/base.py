import random

from houston.system import System

class MissionGenerator(object):

    def __init__(self, system, image, threads, max_num_actions):
        assert isinstance(system, System)
        assert isinstance(image, str)
        assert isinstance(threads, int)
        assert isinstance(max_num_actions, int)
        assert threads > 0
        assert max_num_actions > 0

        self.__system = system
        self.__image = image
        self.__threads = threads
        self.__max_num_actions = max_num_actions

        self._fetch_lock = threading.Lock()
        self._contents_lock = threading.Lock()

        self.__rng = None
        self.__resource_limits = None
        self.__resource_usage = None
        self.__start_time = None


    @property
    def image(self):
        """
        The name of the Docker image used by the system under test.
        """
        return self.__image


    @property
    def system(self):
        """
        The system under test.
        """
        return self.__system


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


    def outcome(self, mission):
        """
        Returns the outcome for a previously-executed mission.
        """
        return self.__outcomes[mission]


    def tick(self):
        """
        Used to measure the running time of the current generation trial.
        """
        self.__resource_usage.running_time = \
            timeit.default_timer() - self.__start_time


    def generate(self, seed, resource_limits):
        assert isinstance(seed, int)

        self.prepare(system, resource_limits)

        self.__start_time = timeit.default_timer()

        
        # return a reduced mission suite
        return self.reduce()


    def reduce(self):
        """
        """
        # TODO remove all failures from the history list
        return self.__history


    def prepare(self, seed, resource_limits):
        """
        Prepares the state of this generator immediately before beginning a
        new generation trial.
        """
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
        self._fetch_lock.acquire()
        try:
            self.tick()

            # check if there are no jobs left
            if self.exhausted():
                return None

            # RANDOM:
            self.resource_usage.num_missions += 1
            return self.generate_mission()

        finally:
            self._fetch_lock.release()


class RandomMissionGenerator(MissionGenerator):
    def __init__(self):
        pass


    def generate_mission(self):
        schemas = self.system.schemas.values()
        actions = []
        for _ in range(self.rng.randint(1, self.max_num_actions)):
            schema = self.rng.choice(schemas)
            actions.append(self.generate_action(schema))

        return Mission(self.__env, self.__initial_state, actions)
