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
        self.__actionGenerators = actionGenerators


    def getInitialState(self):
        return self.__initialState


    def getEnvironment(self):
        return self.__env


class RandomBugDetector(BugDetector):
    pass


class RandomDirectedBugDetector(BugDetector):
    
    def generate(self):
        schemas = list(self.getSystem().getSchemas().values())

        # seed the initial contents of the pool
        m = Mission(self.getEnvironment(), self.getInitialState(), [])
        pool = set([m])

        # a list of missions that were executed
        history = []

        # a dictionary from missions to end states
        endStates = {m: self.getInitialState()}

        # a dictionary from missions to outcomes
        outcomes = {}

        # the set of pruned mission paths
        tabu = set()

        # the set of failing missions, believed to be indicate of an
        # underlying fault
        failures = set()

        # sample N missions with replacement from the pool
        N = 10
        parents = random.sample(pool, N)
        children = set()

        # generate candidate missions using the selected parents
        # discard any missions that belong to the tabu list
        for parent in parents:
            schema = random.choice(schemas)
            action = self.generateAction(schema)

            actions = parent.getActions() + [action]

            child = Mission(parent.getEnvironment(), parent.getInitialState(), actions)

            # TODO: implement tabu list
            # if child in tabu:
            #    continue

            children.append(child)

        # TODO evaluate each of the missions (in parallel, using a thread pool)
        results = {child: cntr.execute(child) for child in children}

        # process the results for each child
        for (child, outcome) in results.items():
            if outcome.failed():
                # if the last action failed, mark the mission as fault-revealing
                if outcome.lastActionFailed():
                    failures[child] = outcome
                    tabu[child] = outcome

                # if an earlier action failed, add the failing segment of the
                # mission to the tabu list
                else:
                    blah

            # if the test was successful, add it to the pool
            else:
                pool[child] = outcome
             
        
    def generateAction(self, schema):
        name = schema.getName()
        generators = self.getGenerators()
        if name in generators:
            g = generators[name]
            return g.generate()

        schema.generate()
