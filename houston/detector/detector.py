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
        print("shutting down worker: {}".format(self))
        if self.__container is not None:
            houston.destroyContainer(self.__container)
            self.__container = None


class BugDetectorSummary(object):
    @staticmethod
    def fromJSON(jsn):
        jsn = jsn['summary']
        systm = houston.getSystem(jsn['settings']['system'])
        image = jsn['settings']['image']

        resourceUsage = ResourceUsage.fromJSON(jsn['resources']['used'])
        resourceLimits = ResourceLimits.fromJSON(jsn['resources']['limits'])

        history = \
            [Mission.fromJSON(m['mission']) for m in jsn['history']]
        failures = \
            set(Mission.fromJSON(m['mission']) for m in jsn['failures'])

        outcomes = \
            [(h['mission'], h['outcome']) for h in jsn['history']]
        outcomes = \
            [(Mission.fromJSON(m), MissionOutcome.fromJSON(o)) for (m, o) in outcomes]
        outcomes = {m: o for (m, o) in outcomes}

        return BugDetectorSummary(systm, image, history, outcomes, failures, resourceUsage, resourceLimits)


    def __init__(self, systm, image, history, outcomes, failures, resourceUsage, resourceLimits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
        assert (isinstance(systm, system.System) and systm is not None)
        assert (isinstance(image, str) or isinstance(image, unicode))
        assert (image is not None)
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

    
    def getNumMissions(self):
        return len(self.__history)

    
    def getNumFailures(self):
        return len(self.__failures)


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
        self.__resourceLimits = resourceLimits
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
            print("Preparing...")
            self.prepare(systm, image, seed, resourceLimits)
            print("Prepared")

            # initialise worker threads
            self.__workers = []
            print("constructing workers...")
            for _ in range(self.__threads):
                self.__workers.append(MissionPoolWorker(self))
            print("constructed workers")
            
            # begin tracking resource usage
            self.__resourceUsage = ResourceUsage()
            self.__startTime = timeit.default_timer()

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


class RandomBugDetectorSummary(BugDetectorSummary):
    @staticmethod
    def fromJSON(jsn):
        base = BugDetectorSummary.fromJSON(jsn)
        return RandomBugDetectorSummary(base)


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
