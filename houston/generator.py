import random
import mission
import system
import test

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
        assert (isinstance(environment, system.Environment) and not environment is None)
        self.__system = systm
        self.__environment = environment
        self.__initialState = initialState


    def getSystem(self):
        """
        Returns a description of the system for which this generator should
        generate test suites.
        """
        return self.__system


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

    def generate(self, characteristics, limits):
        assert(isinstance(characteristics, test.MissionSuiteCharacteristics))
        assert(not characteristics is None)

        missions = test.MissionSuite()
        while not missions.satisfiesMissionNumber(characteristics):
            m = self.generateMission(characteristics, limits)
            missions.add(m)

        return missions

        #stateBefore


    def generateMission(self, missions, characteristics, limits):
        """
        Generates a single Mission at random.

        :param  characteristics:    the desired characteristics of the mission\
                                    suite to which this test will belong.
        :param  limits              limit of the avaliable resources to generate
                                    the missionsuite

        :returns    A randomly-generated Mission instance
        """
        assert (isinstance(characteristics, test.MissionSuiteCharacteristics))
        assert (not characteristics is None)

        # generate an initial state
        env = self.generateEnvironment()
        startState = self.generateInitialState(env)
        currentState = startState
        nextState = None

        actions = []
        schemas = self.getSystem().getActionSchemas()

        maxNumActions = characteristics.getMaxNumActionsPerMission()
        while not len(actions) <= maxNumActions:

            # which schemas can we *possibly* satisfy?
            # - find preconditions that DO NOT interact with parameters
            # - does the current state satisfy those preconditions? If not, we
            #   can't generate an action of that schema! Discard.
            legalSchemas = set()
            for schema in schemas.iteritems(): # TODO what's the type?

                # is it impossible to satisfy this schema in the current state?
                for precondition in schema.getPreconditions():
                    if not precondition.usesParameters():
                        if not precondition.satisfiedBy(startState, {}):
                            continue
                legalSchemas.add(schema)
            
            # attempt to generate an action belonging to any of the legal
            # schemas
            for attempt in range(limits.getMaxNumRetries()):
                schema = random.choice(legalSchemas)
                (action, nextState) = self.generateAction(schema, currentState)

                # TODO: error checking

                # check that preconditions and invariants are satisfied
                predicates = schema.getPreconditions() + schema.getInvariants()
                if all(p.satisfiedBy(newState, params) for p in predicates):
                    actions.append(action)
                    currentState = nextState

            # have we exhausted the max. num. retries? Throw an error.
            if attempt == (limits.getMaxNumRetries() - 1):
                raise Exception('exhausted max. num. retries when generating action.')

        return mission.Mission(env, startState, actions)

    
    def generateEnvironment(self):
        return self.__environment


    def generateInitialState(self, env):
        return self.__initialState


    def generateAction(self, schema, stateBefore):
        """
        Generates an action at random

        :param      schema: the schema to which this action belongs, given as\
                            an ActionSchema instance
        :param      stateBefore:    the state of the system immediately before\
                                    the start of the action


        :returns    A randomly-generated Action instance
        """
        assert(isinstance(schema, system.ActionSchema) and not schema is None)

        params = {}
        for parameter in schema.getParameters():
            name = parameter.getName()

            # if a generator was supplied, use that to generate a suitable
            # value, otherwise use the default generator
            value = parameter.generate()
            params[name] = value
            stateBefore.updateInternalState(name, value)

        return mission.Action(schema.getName(), params), stateBefore

class DirectedGenerator(TestSuiteGenerator):
    pass
