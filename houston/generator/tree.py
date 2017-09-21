from houston.system import System
from houston.branch import BranchID, BranchPath
from houston.mission import Mission, MissionOutcome
from houston.action import ActionOutcome, Action, ActionGenerator


class TreeBasedMissionGenerator(MissionGenerator):
    def __init__(self,
                 system,
                 image,
                 initial_state,
                 env,
                 threads = 1,
                 action_generators = [],
                 max_num_actions = 10):
        super(TreeBasedMissionGenerator, self).__init__(system, image, threads, action_generators, max_num_actions)
        self.__seed_mission = Mission(env, initial_state, [])

    
    @property
    def seed_mission(self):
        """
        The mission that is used as a seed when generating new missions.
        """
        return self.__seed_mission
    

    def record_outcome(self, mission, outcome):
        """
        Once the outcome of a mission has been determined, this function is
        reponsible for guiding the generation of new missions based on the
        outcome of that mission.
        
        If the mission failed, it indicates that either:

            (a) there is either a bug in the system under test,
            (b) there is non-determinism in the outcome of missions, or
            (c) the system is poorly specified.

        If the mission was successful, a new mission is generated for each
        (reachable) child node in the behaviour graph.
        """
        super(TreeBasedMissionGenerator, self).record_outcome(mission, outcome)

        self._contents_lock.acquire()
        try:
            intended_path = self.__intended_paths[mission]
            executed_path = self.executed_path(mission)
            del self.__intended_paths[mission]

            if outcome.passed:
                self.expand(mission)
            else:
                # TODO: should we prune both?
                self.prune(intended_path)
                self.prune(executed_path)
        finally:
            self.__running.remove(mission)
            self._contents_lock.release()


    def prune(self, path):
        """
        Removes a given branch path from the search space, preventing further
        exploration along that path.
        """
        assert isinstance(path, BranchPath)
        printflush("Adding path to tabu list: {}".format(path))
        self.__queue = set(m for m in self.__queue if not self.__intended_paths[m].startswith(path))


    def prepare(self, seed, resource_limits):
        super(TreeBasedMissionGenerator, self).prepare(seed, resource_limits)

        self.__intended_paths = {}
        self.__queue = set()
        self.__running = set() # could we just use a count?
        self.expand(self.seed_mission)


    def exhausted(self):
        """
        The search is exhausted when either its resource limit has been hit, or
        there are no jobs running and no jobs queued (implying that the search
        space has been exhausted).
        """
        if super(TreeBasedMissionGenerator, self).exhausted():
            return True
        return self.__queue == set() and self.__running == set()


    def generator(self):
        """
        Implements a thread-safe mission generator.
        """
        self._fetch_lock.acquire()
        try:
            while True:
                # TODO do we always need to grab the lock here? overly pessimistic.
                self._contents_lock.acquire() 
                try:
                    self.tick()
                    if self.exhausted():
                        return

                    # check the queue
                    if self.__queue != set():
                        mission = self._rng.sample(self.__queue, 1)[0]
                        self.__queue.remove(mission)
                        self.__running.add(mission)
                        self.resource_usage.num_missions += 1
                        yield mission

                    # wait until there is a job in the queue (or resources have
                    # been exhausted)
                    time.sleep(0.05)
                finally:
                    self._contents_lock.release()

        finally:
            self._fetch_lock.release()


    def expand(self, mission):
        """
        Called after a mission has finished executing
        """
        systm = self.system
        branches = systm.branches
        state = self.get_end_state(mission)
        env = mission.environment
        path = self.executed_path(mission)

        # if we've hit the action limit, don't expand
        if self.max_num_actions is not None and self.max_num_actions == mission.size:
            return

        # otherwise, explore each branch
        branches = [b for b in branches if b.is_satisfiable(state, env)]
        for b in branches:
            p = path.extended(b)
            a = self.generate_action(b, env, state)
            m = mission.extended(a)
            self.__queue.add(m)
            self.__intended_paths[m] = p


    def generate_action(self, branch, env, state):
        """
        TODO: add branch-specific action generators
        """
        generator = self.get_generator(branch.schema)
        if generator is not None:
            return generator.generate_action_with_state(state, env, self._rng)
        return branch.generate(state, env, self._rng) 
