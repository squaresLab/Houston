import random
import mission
import system
import state
import test
import time

"""
The generator module is responsible for providing a number of different test
suite generation approaches.

- maximise code coverage
- maximise (behavioural) diversity
- maximise mutant score
- minimise expected time to cause failure (obtained via use of mutants)
"""

class TestSuiteGenerator(object):
    """
    TestSuiteGenerator defines a common interface for all test suite
    generation approaches.
    """

    def __init__(self, systm, environment, initialState):
        """
        Constructs a test suite generator for a given system.

        :param      systm           system-under-test
        :param      environment     the environment in which the missions \
                                    should be conducted
        :param      initialState    the initial state of the system for each \
                                    mission
        """
        assert (isinstance(systm, system.System) and not systm is None)
        assert (isinstance(environment, state.Environment) and not environment is None)
        assert (isinstance(initialState, state.State) and not initialState is None)
        self.__system = systm
        self.__environment = environment
        self.__initialState = initialState


    def getSystem(self):
        """
        Returns a description of the system for which this generator should
        generate test suites.
        """
        return self.__system


    def getEnvironment(self):
        """
        Returns the mission suite environment
        """
        return self.__environment


    def getInitialState(self):
        """
        Returns the mission suite initial state
        """
        return self.__initialState


    def generate(self, characteristics, limits):
        """
        Using no more than a specified set of resources, this method generates
        a set of missions that satisfy given characteristics using the strategy
        associated with this generator.

        :param  characteristics A description of the desired characteristics of the
                                resulting test suite.
        :param  limits          A description of the limited resources
                                available for the purposes of generating the
                                test suite.

        :return A MissionSuite object.
        """

        # ResourceUsage and ResourceLimit objects
        raise NotImplementedError


class RandomGenerator(TestSuiteGenerator):
    """
    The random generator iteratively constructs a test suite (at random,
    without any direction) until the resulting suite satisfies the
    characteristics specified by the user (e.g., number of tests, expected
    running time).

    What if the generator fails to generate such a set within the given time
    limits? Should it return the current state of its set, or should it just
    throw an exception?
    """

    def generate(self, characteristics, resources):
        assert (isinstance(characteristics, test.MissionSuiteCharacteristics))
        assert (isinstance(resources, test.GeneratorResourceLimits))
        assert(not characteristics is None)
        assert(not resources is None)

        missions = test.MissionSuite()

        generationMaxTime = resources.getMaxTime()
        startGenerationTime = time.time()

        missionSuiteTime = 0.0
        missionSuiteMaxTime = characteristics.getMaxTime()

        while not missions.satisfiesMissionNumber(characteristics.getMaxMissions()):
            currentElapsedTime = time.time() - startGenerationTime
            # Checks that the generation is not taking longer than the specified.
            if currentElapsedTime >= generationMaxTime:
                break
            # Checks that the mission suite doesn't take longer than the specified.
            if missionSuiteTime >= missionSuiteMaxTime and generationMaxTime:
                break
            # Generates a mission
            m = self.generateMission(characteristics, resources)
            missionSuiteTime += m.getExpectedMissionDuration(self.getSystem())

            missions.add(m)
        return missions


    def generateMission(self, characteristics, resources):
        """
        Generates a single Mission at random.

        :param  characteristics:    the desired characteristics of the mission\
                                    suite to which this test will belong.
        :param  limits              limit of the avaliable resources to generate
                                    the missionsuite

        :returns    A randomly-generated Mission instance
        """
        assert (isinstance(characteristics, test.MissionSuiteCharacteristics))
        assert (isinstance(resources, test.GeneratorResourceLimits))
        assert (not characteristics is None)
        assert (not resources is None)

        # generate an initial state
        env = self.generateEnvironment()
        startState = self.generateInitialState(env)
        schemas = list(self.getSystem().getActionSchemas().values())

        missionTime = 0.0
        missionMaxTime = characteristics.getMissionCharacteristics().getMaxTime()
        actionMaxTime = characteristics.getActionCharacteristics().getMaxTime()

        actions = []
        for _ in range(characteristics.getMissionCharacteristics().getMaxActions()):
            if missionTime >= missionMaxTime:
                break
            schema = random.choice(schemas)
            for __ in range(resources.getMaxNumRetries()):
                action = self.generateAction(schema)
                actionTime = schema.computeTimeout(action, startState, env)

                if actionTime < actionMaxTime:
                    actions.append(action)
                    missionTime += actionTime
                    break

        return mission.Mission(env, startState, actions)


    def generateEnvironment(self):
        return self.getEnvironment()


    def generateInitialState(self, env):
        return self.getInitialState()


    def generateAction(self, schema):
        """
        Generates an action belonging to a particular schema at random

        :param  schema:         the schema to which this action belongs, given \
                                as an ActionSchema instance.

        :returns    A randomly-generated Action instance, belonging to the \
                    given schema.
        """
        assert (isinstance(schema, system.ActionSchema) and not schema is None)


        params = {}
        for parameter in schema.getParameters():
            name = parameter.getName()

            # if a generator was supplied, use that to generate a suitable
            # value, otherwise use the default generator
            value = parameter.generate()
            params[name] = value

        return mission.Action(schema.getName(), params)


class IncrementalGenerator(TestSuiteGenerator):
    pass

    def __init__(self):
        self.__initialStates = blah

    
    def generate(self):
        schemas = list(self.getSystem().getSchemas().values())

        tabu = set()
        failures = set()
        pool = set(Mission(s, []) for s in self.__initialStates)

        # sample N missions with replacement from the pool
        N = 10
        parents = random.sample(pool, N)
        children = set()

        # generate candidate missions using the selected parents
        # discard any missions that belong to the tabu list
        for parent in parents:
            schema = random.choice(schemas)
            action = self.generateAction(schema)

            child = Mission(parent.getContext(), parent.getActions() + [action]) # TODO: Mission::getContext

            if child in tabu: # TODO: optimise (via hashing)
                continue

            children.append(child)

        # evaluate each of the missions (in parallel, using a thread pool)
        results = {child: cntr.execute(child) for child in children}

        #


    # TODO: implement via ActionGenerator
    def generateAction(self, schema):
        pass
