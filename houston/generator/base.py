import random
import threading

from houston.system import System
from houston.generator.resources import ResourceUsage, ResourceLimits


class MissionGenerator(object):

    def __init__(self, system, image, threads = 1, action_generators = [],  max_num_actions = 10):
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


        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__action_generators = {}
        for g in action_generators:
            name = g.schema_name
            assert name not in self.__action_generators
            self.__action_generators[name] = g


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


    def executed_path(self, m):
        """
        Returns the path that was taken when a given mission was executed.
        """
        if m.is_empty():
            return BranchPath([])
        outcome = self.__outcomes[m]
        return outcome.executed_path()


    def tick(self):
        """
        Used to measure the running time of the current generation trial.
        """
        self.__resource_usage.running_time = \
            timeit.default_timer() - self.__start_time


    def generate(self, seed, resource_limits):
        assert isinstance(seed, int)

        try:
            print("Preparing..."),
            self.prepare(seed, resource_limits)
            print("[OK]")

            # initialise worker threads
            self.__workers = []
            print("constructing workers...")
            for _ in range(self.__threads):
                self.__workers.append(MissionPoolWorker(self))
            print("constructed workers")
            
            # begin tracking resource usage
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()

            print("starting workers...")
            for w in self.__workers:
                w.start()
            print("started all workers")
            while True:
                if not any(w.is_alive() for w in self.__workers):
                    break
                time.sleep(0.2)

            self.tick()
            return self.summarise()
        finally:
            print("shutting down...")
            for worker in self.__workers:
                print("killing worker: {}".format(worker))
                worker.shutdown()
            self.__workers = []



        
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


    def execute_mission(self, mission, container):
        """
        Executes a given mission using a provided container.
        """
        print("executing mission..."),
        outcome = container.execute(mission)
        self.record_outcome(mission, outcome)
        print("\t[DONE]")
        return outcome


    def record_outcome(self, mission, outcome):
        """
        Records the outcome of a given mission. The mission is logged to the
        history, and its outcome is stored in the outcome dictionary. If the
        mission failed, the mission is also added to the set of failed
        missions.
        """
        self.__history.append(mission)
        self.__outcomes[mission] = outcome

        if outcome.failed():
            self.__failures.add(mission)


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
