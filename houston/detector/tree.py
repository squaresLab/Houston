from base import BugDetectorSummary, BugDetector
from houston.system import System
from houston.branch import BranchID, BranchPath
from houston.mission import Mission, MissionOutcome
from houston.action import ActionOutcome, Action, ActionGenerator


class TreeBasedBugDetectorSummary(BugDetectorSummary):
    """
    Used to provide a summary of a test generation trial that used the
    tree-based test generation strategy.
    """
    @staticmethod
    def from_json(jsn):
        base = BugDetectorSummary.from_json(jsn)
        flaky = [f['mission'] for f in jsn['summary']['flaky']]
        flaky = set(Mission.from_json(f) for f in flaky)
        return TreeBasedBugDetectorSummary(base, flaky)


    def __init__(self, base, flaky):
        """
        TODO: aspects of this feel hacky.
        """
        assert isinstance(base, BugDetectorSummary)
        assert isinstance(flaky, set)
        assert all(isinstance(m, Mission) for m in flaky)

        super(TreeBasedBugDetectorSummary, self).__init__(base.system,
                                                          base.image,
                                                          base.history,
                                                          base.outcomes,
                                                          base.failures,
                                                          base.resource_usage,
                                                          base.resource_limits)
        self.__flaky = flaky


    @property
    def num_flaky(self):
        return len(self.__flaky)


    def to_json(self):
        jsn = super(TreeBasedBugDetectorSummary, self).to_json()

        flaky = [(m, self.get_outcome(m)) for m in self.__flaky]
        flaky = [{'mission': m.to_json(), 'outcome': o.to_json()} for (m, o) in flaky]

        jsn['summary']['flaky'] = flaky
        jsn['summary']['settings']['algorithm'] = 'tree'

        return jsn


class TreeBasedBugDetector(BugDetector):
    """
    Description.
    """
    def __init__(self, initial_state, env, threads = 1, action_generators = [], max_num_actions = 10):
        super(TreeBasedBugDetector, self).__init__(threads, action_generators, max_num_actions)
        self.__seed = Mission(env, initial_state, [])


    def summarise(self):
        summary = super(TreeBasedBugDetector, self).summarise()
        summary = TreeBasedBugDetectorSummary(summary, self.__flaky)
        return summary


    def record_outcome(self, mission, outcome):
        super(TreeBasedBugDetector, self).record_outcome(mission, outcome)

        self._contents_lock.acquire()
        try:
            intended_path = self.__intended_paths[mission]
            executed_path = self.get_executed_path(mission)
            del self.__intended_paths[mission]

            if not outcome.failed:
                self.expand(mission)
            else:
                self.prune(executed_path)
                if intended_path != executed_path:
                    self.__flaky.add(mission)
        finally:
            self.__running.remove(mission)
            self._contents_lock.release()

        # if the mission failed but didn't follow the intended path, we've
        # found a flaky path.
            # TODO: access!
            # self.__failures.remove(mission)
            # for other in self.__failures:
            #     otherPath = self.getExecutedPath(other)
            #     if otherPath.startswith(executedPath):
            #         self.__flaky.add(other)
            #         self.__failures.remove(other)


    def prune(self, path):
        assert (isinstance(path, BranchPath))
        printflush("Adding path to tabu list: {}".format(path))
        self.__queue = set(m for m in self.__queue if not self.__intended_paths[m].startswith(path))


    def prepare(self, systm, image, seed, resource_limits):
        super(TreeBasedBugDetector, self).prepare(systm, image, seed, resource_limits)

        self.__flaky = set()
        self.__intended_paths = {}
        self.__queue = set()
        self.__running = set()
        self.expand(self.__seed)


    def exhausted(self):
        if super(TreeBasedBugDetector, self).exhausted():
            return True
        return self.__queue == set() and self.__running == set()


    def get_next_mission(self):
        self._fetch_lock.acquire()
        try:
            while True:
                self.tick()

                # check if there are no jobs left
                self._contents_lock.acquire()
                try:
                    if self.exhausted():
                        return None

                    # check if there is a job in the queue
                    if self.__queue != set():
                        printflush("Generating mission")
                        mission = self._rng.sample(self.__queue, 1)[0]
                        self.__queue.remove(mission)
                        self.__running.add(mission)
                        self.resource_usage.num_missions += 1
                        return mission
                    
                finally:
                    self._contents_lock.release()

                # if there isn't we need to wait until pending jobs
                # are finished
                time.sleep(0.1)

        finally:
            self._fetchLock.release()


    def expand(self, mission):
        """
        Called after a mission has finished executing
        """
        systm = self.system
        branches = systm.branches
        state = self.get_end_state(mission)
        env = mission.environment
        path = self.get_executed_path(mission)

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
