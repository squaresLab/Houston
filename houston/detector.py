import copy
import random
import timeit

from mission import Mission

class ResourceUsage(object):
    """
    Simple data structure used to maintain track of what resources have been
    consumed over the course of a bug detection trial.
    """
    def __init__(self):
        self.numMissions = 0
        self.runningTime = 0.0


class ResourceLimits(object):
    """
    A convenience class used to impose limits on the bug detection process.
    """
    def __init__(self, numMissions = None, runningTime = None):
        self.__numMissions = numMissions
        self.__runningTime = runningTime


    def reached(self, usage):
        if self.reachedMissionLimit(self, usage.numMissions):
            return True
        if self.reachedTimeLimit(self, usage.runningTime):
            return True
        return False


    def reachedMissionLimit(self, numMissions):
        return  self.__numMissions is not None and \
                    numMissions >= self.__numMissions

    
    def reachedTimeLimit(self, runningTime):
        return  self.__runningTime is not None and \
                    runningTime >= self.__runningTime


class BugDetectionSummary(object):
    def __init__(self, history, outcomes, resourceUsage, resourceLimits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
        self.__history = history
        self.__outcomes = outcomes
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
        summary = {
            'resources': resources,
            'history': [self.__history
        }
        return {'summary': summary}


class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self, threads = 1, actionGenerators = []):
        assert (isinstance(threads, int) and threads is not None)
        assert (threads >= 1)
        assert (isinstance(actionGenerators, list) and actionGenerators is not None)
        assert (all(isinstance(g) for g in actionGenerators))

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__actionGenerators = {}
        for g in actionGenerators:
            name = g.getSchemaName()
            assert not (name in self.__actionGenerators)
            self.__actionGenerators[name] = g

   
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
        raise UnimplementedError


    def generateAction(self, schema):
        """
        Generates an instance of a given action schema at random.
        """
        name = schema.getName()
        if name in self.__actionGenerators:
            g = self.__actionGenerators[name]
            return g.generate()

        return schema.generate()
        

class IncrementalBugDetector(BugDetector):
    
    def __init__(self, initialState, env, threads = 1, actionGenerators = []):
        super(IncrementalBugDetector, self).__init__(threads, actionGenerators)
        self.__initialState = initialState
        self.__env = env

        
    def getInitialState(self):
        return self.__initialState


    def getEnvironment(self):
        return self.__env


    def detect(self, systm, image, resourceLimits):
        self.__containers = [houston.createContainer(systm, image)]

        # initial seed
        m = Mission(self.getEnvironment(), self.getInitialState(), [])

        self.__startTime = timeit.default_timer()
        self.__usage = ResourceUsage()
        self.__pool = set([m])
        self.__endStates = {m: self.getInitialState()}
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self.__tabu = set()

        # keep running tests until we hit the resource limit
        while not resourceLimits.reached(resourceUsage):
            self.runGeneration()

        # kill the containers
        for container in self.__containers:
            container.destroy()

        return BugDetectionSummary(self.__usage, resourceLimits)
        

    def executeMissions(self, missions):
        # TODO use a thread pool!
        # TODO enforce limits
        outcomes = {m: self.executeMission(m) for m in missions}
        for (m, outcome) in outcomes.items():
            self.__history.append(m)
            self.__outcomes[m] = outcome
            self.__endStates[m] = outcome.getEndState()

            # update resource usage
            self.__resourceUsage.numMissions += 1
            self.__resourceUsage.runningTime = \
                timeit.default_timer() - self.__startTime

            if m.failed():
                self.__failures.add(m)


    def executeMission(self, mission):
        return self.__containers[0].execute(mission)


    def nextGeneration(self):
        N = 10
        parents = random.sample(pool, N)
        children = set()

        # generate candidate missions using the selected parents
        # discard any missions that belong to the tabu list
        for parent in parents:
            schema = random.choice(schemas)
            action = self.generateAction(schema)
            actions = parent.getActions() + [action]

            # TODO: implement tabu list
            child = Mission(parent.getEnvironment(), parent.getInitialState(), actions)
            children.add(child)

        self.executeMissions(children)

        for child in children:
            if not outcome.failed(): # TODO: update tabu list
                pool.add(child)
