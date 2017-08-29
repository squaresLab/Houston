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
    def fromJSON(jsn):
        base = BugDetectorSummary.fromJSON(jsn)
        flaky = [f['mission'] for f in jsn['summary']['flaky']]
        flaky = set(Mission.fromJSON(f) for f in flaky)
        return TreeBasedBugDetectorSummary(base, flaky)


    def __init__(self, base, flaky):
        """
        TODO: aspects of this feel hacky.
        """
        assert (isinstance(base, BugDetectorSummary))
        assert (isinstance(flaky, set))
        assert (all(isinstance(m, Mission) for m in flaky))

        super(TreeBasedBugDetectorSummary, self).__init__(base.getSystem(),
                                                          base.getImage(),
                                                          base.getHistory(),
                                                          base.getOutcomes(),
                                                          base.getFailures(),
                                                          base.getResourceUsage(),
                                                          base.getResourceLimits())
        self.__flaky = flaky


    def getNumFlaky(self):
        return len(self.__flaky)


    def toJSON(self):
        jsn = super(TreeBasedBugDetectorSummary, self).toJSON()

        flaky = [(m, self.getOutcome(m)) for m in self.__flaky]
        flaky = [{'mission': m.toJSON(), 'outcome': o.toJSON()} for (m, o) in flaky]

        jsn['summary']['flaky'] = flaky
        jsn['summary']['settings']['algorithm'] = 'tree'

        return jsn


class TreeBasedBugDetector(BugDetector):
    """
    Description.
    """
    def __init__(self, initialState, env, threads = 1, actionGenerators = [], maxNumActions = 10):
        super(TreeBasedBugDetector, self).__init__(threads, actionGenerators, maxNumActions)
        self.__seed = Mission(env, initialState, [])


    def summarise(self):
        summary = super(TreeBasedBugDetector, self).summarise()
        summary = TreeBasedBugDetectorSummary(summary, self.__flaky)
        return summary


    def recordOutcome(self, mission, outcome):
        super(TreeBasedBugDetector, self).recordOutcome(mission, outcome)

        self._contentsLock.acquire()
        try:
            intendedPath = self.__intendedPaths[mission]
            executedPath = self.getExecutedPath(mission)
            del self.__intendedPaths[mission]

            if not outcome.failed():
                self.expand(mission)
            else:
                self.prune(executedPath)
                if intendedPath != executedPath:
                    self.__flaky.add(mission)
        finally:
            self.__running.remove(mission)
            self._contentsLock.release()

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
        self.__queue = set(m for m in self.__queue if not self.__intendedPaths[m].startswith(path))


    def prepare(self, systm, image, seed, resourceLimits):
        super(TreeBasedBugDetector, self).prepare(systm, image, seed, resourceLimits)

        self.__flaky = set()
        self.__intendedPaths = {}
        self.__queue = set()
        self.__running = set()
        self.expand(self.__seed)


    def exhausted(self):
        if super(TreeBasedBugDetector, self).exhausted():
            return True
        return self.__queue == set() and self.__running == set()


    def getNextMission(self):
        self._fetchLock.acquire()
        try:
            while True:
                self.tick()

                # check if there are no jobs left
                self._contentsLock.acquire()
                try:
                    if self.exhausted():
                        return None

                    # check if there is a job in the queue
                    if self.__queue != set():
                        printflush("Generating mission")
                        mission = self._rng.sample(self.__queue, 1)[0]
                        self.__queue.remove(mission)
                        self.__running.add(mission)
                        self.getResourceUsage().numMissions += 1
                        return mission
                    
                finally:
                    self._contentsLock.release()

                # if there isn't we need to wait until pending jobs
                # are finished
                time.sleep(0.1)

        finally:
            self._fetchLock.release()


    def expand(self, mission):
        """
        Called after a mission has finished executing
        """
        systm = self.getSystem()
        branches = systm.getBranches()
        state = self.getEndState(mission)
        env = mission.getEnvironment()
        path = self.getExecutedPath(mission)

        # if we've hit the action limit, don't expand
        maxNumActions = self.getMaxNumActions()
        if maxNumActions is not None and maxNumActions == mission.size():
            return

        # otherwise, explore each branch
        branches = [b for b in branches if b.isSatisfiable(state, env)]
        for b in branches:
            p = path.extended(b)
            a = self.generateAction(b, env, state)
            m = mission.extended(a)
            self.__queue.add(m)
            self.__intendedPaths[m] = p


    def generateAction(self, branch, env, state):
        """
        TODO: add branch-specific action generators
        """
        generator = self.getGenerator(branch.getSchema())
        if generator is not None:
            return generator.generateActionWithState(state, env, self._rng)
        return branch.generate(state, env, self._rng) 
