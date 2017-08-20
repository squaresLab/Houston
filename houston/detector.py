import copy
import random
import timeit
import houston
import system

from multiprocessing.pool import ThreadPool

from mission import Mission, MissionOutcome
from action import ActionOutcome, Action
from branch import BranchID, BranchPath


class AllPathsExplored(Exception):
    """
    Used to indicate that all paths have been explored.
    """
    pass


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
        print 'Total running time: {}'.format(usage.runningTime)
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
        assert (all(isinstance(g, system.ActionGenerator) for g in actionGenerators))

        self.__maxNumActions = maxNumActions

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__actionGenerators = {}
        for g in actionGenerators:
            name = g.getSchemaName()
            assert not (name in self.__actionGenerators)
            self.__actionGenerators[name] = g


    def prepare(self, systm, image, resourceLimits):
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


    def cleanup(self):
        """
        Cleans up the state of this bug detector at the end of a bug detection
        trial.
        """
        pass


    def exhausted(self):
        """
        Used to determine whether the resource limit for the current bug
        detection session has been hit.
        """
        return self.__resourceLimits.reached(self.__resourceUsage)


    def detect(self, systm, image, resourceLimits):
        """

        :param      systm: the system under test
        :param      image: the name of the Dockerfile that should be used to \
                        containerise the system under test
        :param      resourceLimits: a description of the resources available \
                        to the detection process, given as a ResourceLimits \
                        object

        :returns    a summary of the detection process in the form of a \
                    BugDetectionSummary object
        """
        self.prepare(systm, image, resourceLimits)
        try:
            self.run(systm)
            return self.summarise()
        finally:
            self.cleanup()


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


    def run(self, systm):
        raise NotImplementedError


    def getMaxNumActions(self):
        return self.__maxNumActions


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


    def executeMissions(self, missions):
        # if we've been given more missions than we can execute, trim the list
        missions = list(missions)
        missionLimit = self.__resourceLimits.getNumMissions()
        if missionLimit is not None:
            missionsLeft = missionLimit - self.__resourceUsage.numMissions
            missions = missions[:min(len(missions), missionsLeft)]

        # use a thread pool to distribute the execution
        tPool = ThreadPool(self.__threads)
        outcomes = tPool.map(lambda m: (m, self.executeMission(m)), missions)
        for (mission, outcome) in outcomes:
            self.recordOutcome(mission, outcome)

        # update resource usage
        self.__resourceUsage.numMissions += len(missions)
        self.__resourceUsage.runningTime = \
            timeit.default_timer() - self.__startTime


    def executeMission(self, mission):
        # TODO: temporary!
        print("executing mission...")
        container = houston.createContainer(self.__systm, self.__image)
        try:
            outcome = container.execute(mission)
            print("finished mission!")
            return outcome
        finally:
            container.destroy()


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
    def __init__(self, base, flaky, tabu):
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
        self.__tabu = tabu


    def toJSON(self):
        jsn = super(TreeBasedBugDetectorSummary, self).toJSON()

        tabu = [to.toJSON() for t in self.__tabu]

        flaky = [(m, self.getOutcome(m)) for m in self.__flaky]
        flaky = [{'mission': m.toJSON(), 'outcome': o.toJSON()} for (m, o) in flaky]

        jsn['summary']['tabu'] = tabu
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
        summary = TreeBasedBugDetectorSummary(summary, self.__flaky, self.__tabu)
        return summary


    def recordOutcome(self, mission, outcome):
        super(TreeBasedBugDetector, self).recordOutcome(mission, outcome)

        intendedPath = self.__intendedPaths[mission]
        del self.__intendedPaths[mission]

        if not outcome.failed():
            self.__explored[intendedPath] = mission
            return

        # add the executed mission path to the tabu list
        print("Adding path to tabu list: {}".format(executedPath))
        self.prune(executedPath)

        # if the mission failed but didn't follow the intended path, we've
        # found a flaky path.
        executedPath = self.getExecutedPath(mission)

        if intendedPath != executedPath:
            self.__flaky.add(mission)

            # TODO: access!
            # self.__failures.remove(mission)

            # for other in self.__failures:
            #     otherPath = self.getExecutedPath(other)
            #     if otherPath.startswith(executedPath):
            #         self.__flaky.add(other)
            #         self.__failures.remove(other)


    def prune(self, path):
        assert (isinstance(path, BranchPath) and path is not None)

        # remove redundant path information from tabu list before adding
        self.__tabu = set(p for p in self.__tabu if not p.startswith(path))
        self.__tabu.add(path)

        # remove redundant information
        self.__explored = {p: m for (p, m) in self.__explored if not p.startswith(path)}


    def prepare(self, systm, image, resourceLimits):
        super(TreeBasedBugDetector, self).prepare(systm, image, resourceLimits)
        self.__explored = {}
        self.__tabu = set()
        self.__flaky = set()
        self.__intendedPaths = {}


    def run(self, systm):
        try:
            # TODO: make asynchronous
            while not self.exhausted():
                bffr = []
                for _ in range(self.getNumThreads()):
                    bffr.append(self.generateMission(systm, self.__seed))
                self.executeMissions(bffr)
        except AllPathsExplored:
            return


    def generateAction(self, branch, env, state):
        """
        TODO: add branch-specific action generators
        """
        generator = self.getGenerator(branch.getSchema())
        if generator is not None:
            return generator.generate(state, env)
        return branch.generate(env, state) 


    def generateMission(self, systm, seed):
        branches = systm.getBranches()
        state = self.getEndState(seed)
        env = seed.getEnvironment()
        path = self.getExecutedPath(seed)

        # choose a branch at random
        branches = [b for b in branches if b.isSatisfiable(state, env)]
        branches = [b for b in branches if path.extended(b) not in self.__tabu]

        # check if there are no viable branches
        if not branches:
            
            # if all viable paths in the tree have been explored, raise an
            # `AllPathsExplored` exception
            if not path:
                raise AllPathsExplored

            # otherwise, add the current path to the tabu list, and attempt to
            # generate a mission from the preceding point along the path
            self.prune(path)
            mission = Mission(env,
                              seed.getInitialState(),
                              seed.getActions()[:-1])
            return self.generateMission(systm, mission)

        branch = random.choice(branches)

        # have we already traversed this path?
        if path in self.__explored:
            return self.generateMission(systm, self.__explored[path])

        # if we haven't, generate an action belonging to this branch
        path = path.extended(branch)
        action = self.generateAction(branch, env, state)
        actions = seed.getActions() + [action]
        mission = Mission(env, seed.getInitialState(), actions)

        # record the intended path
        self.__intendedPaths[mission] = path

        return mission


class RandomBugDetectorSummary(BugDetectorSummary):
    def __init__(self, base):
        assert (isinstance(base, BugDetectorSummary) and base is not None)
        super(TreeBasedBugDetectorSummary, self).__init__(base.getSystem(),
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


    def run(self, systm):
        while not self.exhausted():
            self.runGeneration(systm)


    def summarise(self):
        summary = super(RandomBugDetector, self).summarise()
        summary = RandomBugDetectorSummary(summary)
        return summary


    def generateAction(self, schema):
       generator = self.getGenerator(schema)
       if generator is None:
           return schema.generate()
       return generator.generateActionWithoutState(self.__env)


    def runGeneration(self, systm):
        schemas = systm.getActionSchemas().values()
        maxNumActions = self.getMaxNumActions()
        env = self.__env
        initialState = self.__initialState

        bffr = []
        for _ in range(self.getNumThreads()):
            actions = []
            for _ in range(random.randint(1, maxNumActions)):
                schema = random.choice(schemas)
                actions.append(self.generateAction(schema))
            mission = Mission(env, initialState, actions)
            bffr.append(mission)

        self.executeMissions(bffr)
