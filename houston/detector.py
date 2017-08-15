import copy
import random

from mission import Mission

class ResourceUsage(object):

    def __init__(self):
        self.__numMissions = 0


class ResourceLimits(object):
    """
    A convenience class used to impose limits on the bug detection process.
    """
    def __init__(self, numMissions = None):
        self.__numMissions = numMissions


    def reached(self, usage):
        return False


    def reachedMissionLimit(self, numMissions):
        return  self.__numMissions is not None \
                    or numMissions >= self.__numMissions


class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self):
        pass

    
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
        resourceUsage = ResourceUsage()


        summary = BugDetectionSummary(resourceUsage, resourceLimits)
        return summary


class BugDetectionSummary(object):
    def __init__(self, resourceUsage, resourceLimits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
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
            'resources': resources
        }
        return {'summary': summary}


class IncrementalBugDetector(BugDetector):
    
    def __init__(self, initialState, env, actionGenerators):
        self.__initialState = initialState
        self.__env = env

        assert (isinstance(actionGenerators, list) and actionGenerators is not None)
        assert (all(isinstance(g) for g in actionGenerators))

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__actionGenerators = {}
        for g in actionGenerators:
            name = g.getSchemaName()
            assert not (name in self.__actionGenerators)
            self.__actionGenerators[name] = g


    def getInitialState(self):
        return self.__initialState


    def getEnvironment(self):
        return self.__env


    def detect(self, systm, image, resourceLimits):
        container = houston.createContainer(systm, image)

        # initial seed
        m = Mission(self.getEnvironment(), self.getInitialState(), [])

        self.__pool = set([m])
        self.__endStates = {m: self.getInitialState()}
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self.__tabu = set()

        for i in range(10): 
            self.runGeneration()

        return BugDetectionSummary()
        

    def executeMissions(self, missions):
        # TODO use a thread pool!
        # TODO enforce limits
        outcomes = {m: self.executeMission(m) for m in missions}
        for (m, outcome) in outcomes.items():
            self.__history.append(m)
            self.__outcomes.append(outcome)
            self.__endStates.append(outcome.getEndState())

            if m.failed():
                self.__failures.add(m)


    def executeMission(self, mission, container):
        return container.execute(mission)


    def generateAction(self, schema):
        """
        Generates an instance of a given action schema at random.
        """
        name = schema.getName()
        if name in self.__actionGenerators:
            g = self.__actionGenerators[name]
            return g.generate()

        return schema.generate()


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
