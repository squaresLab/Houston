import copy
import random
import timeit
import houston
import system
import time
import threading

from util import printflush

from multiprocessing.pool import ThreadPool

from mission import Mission, MissionOutcome
from action import ActionOutcome, Action, ActionGenerator
from branch import BranchID, BranchPath


class MissionPoolWorker(threading.Thread):
    def __init__(self, detector):
        super(MissionPoolWorker, self).__init__()
        print("creating worker...")
        self.daemon = True # mark as a daemon thread
        self.__detector = detector
        self.__container = houston.createContainer(self.__detector.getSystem(),
                                                   self.__detector.getImage())
        self.__resetCounter()
        # self.start()
        

    def __resetCounter(self):
        self.__counter = 0
        self.__reset = random.randint(3, 5)


    def __prepareContainer(self):
        if self.__counter == self.__reset:
            self.__resetCounter()
            self.__container.reset()
        self.__counter += 1


    def run(self):
        print("running worker: {}".format(self))
        #try:
        while True:
            m = self.__detector.getNextMission()
            if m is None:
                return
            self.__prepareContainer()
            self.__detector.executeMission(m, self.__container)
        #finally:
        #    self.shutdown()


    def shutdown(self):
        print("SHUTTING DOWN WORKER: {}".format(self))
        if self.__container is not None:
            print("MY CONTAINER IS: {}".format(self.__container))
            houston.destroyContainer(self.__container)
            self.__container = None


class ResourceUsage(object):
    """
    Simple data structure used to maintain track of what resources have been
    consumed over the course of a bug detection trial.
    """
    def __init__(self):
        self.numMissions = 0
        self.runningTime = 0.0


    def toJSON(self):
        return {
            'numMissions': self.numMissions,
            'runningTime': self.runningTime
        }


class ResourceLimits(object):
    """
    A convenience class used to impose limits on the bug detection process.
    """
    def __init__(self, numMissions = None, runningTime = None):
        self.__numMissions = numMissions
        self.__runningTime = runningTime


    def reached(self, usage):
        if self.reachedMissionLimit(usage.numMissions):
            return True
        if self.reachedTimeLimit(usage.runningTime):
            return True
        return False


    def getNumMissions(self):
        return self.__numMissions


    def reachedMissionLimit(self, numMissions):
        return  self.__numMissions is not None and \
                    numMissions >= self.__numMissions


    def reachedTimeLimit(self, runningTime):
        return  self.__runningTime is not None and \
                    runningTime >= self.__runningTime


    def toJSON(self):
        return {
            'numMissions': self.__numMissions,
            'runningTime': self.__runningTime
        }


class BugDetectorSummary(object):
    def __init__(self, systm, image, history, outcomes, failures, resourceUsage, resourceLimits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
        assert (isinstance(systm, system.System) and systm is not None)
        assert (isinstance(image, str) and image is not None)
        assert (isinstance(resourceUsage, ResourceUsage) and resourceUsage is not None)
        assert (isinstance(resourceLimits, ResourceLimits) and resourceLimits is not None)
        assert (isinstance(history, list) and history is not None)
        assert (isinstance(outcomes, dict) and outcomes is not None)
        assert (isinstance(failures, set) and failures is not None)
        assert (all(isinstance(m, Mission) for m in failures))

        self.__systm = systm
        self.__image = image
        self.__history = history
        self.__outcomes = outcomes
        self.__failures = failures
        self.__resourceUsage = copy.copy(resourceUsage)
        self.__resourceLimits = resourceLimits


    def toJSON(self):
        """
        Transforms this bug detection summary into a JSON format.
        """
        resources = {
            'used': self.__resourceUsage.toJSON(),
            'limits': self.__resourceLimits.toJSON()
        }

        history = [(m, self.__outcomes[m]) for m in self.__history]
        history = [{'mission': m.toJSON(), 'outcome': o.toJSON()} for (m, o) in history]


        failures = [(m, self.__outcomes[m]) for m in self.__failures]
        failures = [{'mission': m.toJSON(), 'outcome': o.toJSON()} for (m, o) in failures]


        summary = {
            'settings': {
                'system': self.__systm.getIdentifier(),
                'image': self.__image
            },
            'resources': resources,
            'history': history,
            'failures': failures
        }

        return {'summary': summary}


    def getImage(self):
        return self.__image


    def getSystem(self):
        return self.__systm

    
    def getHistory(self):
        return self.__history[:]


    def getOutcome(self, m):
        return self.__outcomes[m]

    
    def getOutcomes(self):
        return self.__outcomes.copy()

    
    def getFailures(self):
        return self.__failures.copy()


    def getResourceUsage(self):
        return copy.copy(self.__resourceUsage)


    def getResourceLimits(self):
        return self.__resourceLimits


class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self, threads = 1, actionGenerators = [], maxNumActions = 10):
        assert (isinstance(maxNumActions, int) and maxNumActions is not None)
        assert (maxNumActions >= 1)
        assert (isinstance(threads, int) and threads is not None)
        assert (threads >= 1)
        assert (isinstance(actionGenerators, list) and actionGenerators is not None)
        assert (all(isinstance(g, ActionGenerator) for g in actionGenerators))

        self._rng = None
        self.__maxNumActions = maxNumActions
        self._fetchLock = threading.Lock()
        self._contentsLock = threading.Lock()

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__actionGenerators = {}
        for g in actionGenerators:
            name = g.getSchemaName()
            assert not (name in self.__actionGenerators)
            self.__actionGenerators[name] = g


    def getNextMission(self):
        self._fetchLock.acquire()
        try:
            self.tick()

            # check if there are no jobs left
            if self.exhausted():
                return None

            # RANDOM:
            self.__resourceUsage.numMissions += 1
            return self.generateMission()

        finally:
            self._fetchLock.release()


    def prepare(self, systm, image, seed, resourceLimits):
        """
        Prepares the state of the bug detector immediately before beginning a
        bug detection trial.
        """
        self.__systm = systm
        self.__image = image
        self.__resourceUsage = ResourceUsage()
        self.__resourceLimits = resourceLimits
        self.__startTime = timeit.default_timer()
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self._rng = random.Random(seed)
            

    def exhausted(self):
        """
        Used to determine whether the resource limit for the current bug
        detection session has been hit.
        """
        return self.__resourceLimits.reached(self.__resourceUsage)


    def detect(self, systm, image, seed, resourceLimits):
        """

        :param      systm: the system under test
        :param      image: the name of the Dockerfile that should be used to \
                        containerise the system under test
        :param      seed:   seed for the RNG
        :param      resourceLimits: a description of the resources available \
                        to the detection process, given as a ResourceLimits \
                        object

        :returns    a summary of the detection process in the form of a \
                    BugDetectionSummary object
        """
        try:
            self.prepare(systm, image, seed, resourceLimits)
            self.__workers = []
            print("constructing workers...")
            for _ in range(self.__threads):
                self.__workers.append(MissionPoolWorker(self))
            print("constructed workers")
            print("starting workers...")
            for w in self.__workers:
                w.start()
            print("started all workers")
            while True:
                if not any(w.isAlive() for w in self.__workers):
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


    def tick(self):
        self.__resourceUsage.runningTime = \
            timeit.default_timer() - self.__startTime


    def summarise(self):
        """
        Returns a summary of the last bug detection trial.
        """
        return BugDetectorSummary(self.__systm,
                                  self.__image,
                                  self.__history,
                                  self.__outcomes,
                                  self.__failures,
                                  self.__resourceUsage,
                                  self.__resourceLimits)

    def getNextMission(self):
        self._fetchLock.acquire()
        try:
            while True:
                self.tick()

                # check if there are no jobs left
                if self.exhausted():
                    return None

                # RANDOM:
                self.__resourceUsage.numMissions += 1
                return self.generateMission()

        finally:
            self._fetchLock.release()


    def getMaxNumActions(self):
        return self.__maxNumActions


    def getSystem(self):
        return self.__systm


    def getImage(self):
        return self.__image

    
    def getResourceUsage(self):
        return self.__resourceUsage


    def getNumThreads(self):
        """
        Returns the number of threads specified.
        """
        return self.__threads

    
    def getExecutedPath(self, m):
        """
        Returns the path that was taken when a given mission was executed.
        """
        if m.isEmpty():
            return BranchPath([])
        outcome = self.__outcomes[m]
        return outcome.getExecutedPath()


    def getEndState(self, m):
        """
        Returns the end state after executing a given mission.
        """
        assert (isinstance(m, Mission) and m is not None)
        if m.isEmpty():
            return m.getInitialState()
        outcome = self.__outcomes[m]
        return outcome.getEndState()


    def getGenerator(self, schema):
        """
        Returns an available generator for a given action schema if there are
        non then it returns None.
        """
        name = schema.getName()
        if name in self.__actionGenerators:
            return self.__actionGenerators[name]
        return None


    def generateMission(self, rng):
        raise NotImplementedError


    def executeMission(self, mission, container):
        print("executing mission...")
        outcome = container.execute(mission)
        self.recordOutcome(mission, outcome)
        print("finished mission!")
        return outcome


    def recordOutcome(self, mission, outcome):
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


class TreeBasedBugDetectorSummary(BugDetectorSummary):
    """
    Used to provide a summary of a tree-based bug detection trial.
    """
    def __init__(self, base, flaky):
        assert (isinstance(base, BugDetectorSummary) and base is not None)
        assert (isinstance(flaky, set) and flaky is not None)
        assert (all(isinstance(m, Mission) for m in flaky))

        super(TreeBasedBugDetectorSummary, self).__init__(base.getSystem(),
                                                          base.getImage(),
                                                          base.getHistory(),
                                                          base.getOutcomes(),
                                                          base.getFailures(),
                                                          base.getResourceUsage(),
                                                          base.getResourceLimits())
        self.__flaky = flaky


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
        assert (isinstance(path, BranchPath) and path is not None)
        printflush("Adding path to tabu list: {}".format(path))
        self.__queue = set(m for m in self.__queue if not self.__intendedPaths[m].startswith(path))


    def prepare(self, systm, image, resourceLimits):
        super(TreeBasedBugDetector, self).prepare(systm, image, resourceLimits)

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
        return branch.generate(env, state, self._rng) 


class RandomBugDetectorSummary(BugDetectorSummary):
    def __init__(self, base):
        assert (isinstance(base, BugDetectorSummary) and base is not None)
        super(RandomBugDetectorSummary, self).__init__(base.getSystem(),
                                                       base.getImage(),
                                                       base.getHistory(),
                                                       base.getOutcomes(),
                                                       base.getFailures(),
                                                       base.getResourceUsage(),
                                                       base.getResourceLimits())


    def toJSON(self):
        jsn = super(RandomBugDetectorSummary, self).toJSON()
        jsn['summary']['settings']['algorithm'] = 'random'
        return jsn


class RandomBugDetector(BugDetector):
    def __init__(self, initialState, env, threads = 1, actionGenerators = [], maxNumActions = 10):
        super(RandomBugDetector, self).__init__(threads, actionGenerators, maxNumActions)
        self.__initialState = initialState
        self.__env = env


    def summarise(self):
        summary = super(RandomBugDetector, self).summarise()
        summary = RandomBugDetectorSummary(summary)
        return summary


    def generateAction(self, schema):
       generator = self.getGenerator(schema)
       if generator is None:
           return schema.generate(self._rng)
       return generator.generateActionWithoutState(self.__env, self._rng)


    def generateMission(self):
        systm = self.getSystem()
        schemas = systm.getActionSchemas().values()
        maxNumActions = self.getMaxNumActions()
        env = self.__env
        initialState = self.__initialState

        actions = []
        for _ in range(self._rng.randint(1, maxNumActions)):
            schema = self._rng.choice(schemas)
            actions.append(self.generateAction(schema))

        return Mission(env, initialState, actions)
