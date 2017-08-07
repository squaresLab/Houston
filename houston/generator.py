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


TODO: We need something to define legal initial states (and that gets
      around the time problem)


      Perhaps the state should be constructed in stages?

      * environment
      * external state (uses environment state as an argument)
      * internal state (uses env., and external states as arguments)

    OR, we don't try to generate these things directly, but rather we allow
    systems to define "InitialParameters" (perhaps something with a better
    name). Each "System" implements a method "generateContext", which builds
    a MissionContext (i.e., internal, external, env.) using a set of initial
    parameters.
"""

class TestSuiteGenerator(object):
    """
    TestSuiteGenerator defines a common interface for all test suite
    generation approaches.
    """

    def __init__(self, systm):
        """
        Constructs a test suite generator for a given system.

        :param      systm           system-under-test
        """
        assert(isinstance(systm, system.System) and not systm is None)

        self.__system = systm


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
        while not missions.satisfies(characteristics):
            m = self.generateMission(characteristics)
            missions.add(m)

        return missions

        #stateBefore
    def generateMission(self, characteristics):
        """
        Generates a single Mission at random.

        :param  characteristics:    the desired characteristics of the mission\
                                    suite to which this test will belong.

        :returns    A randomly-generated Mission instance
        """
        assert(isinstance(characteristics, test.MissionSuiteCharacteristics))
        assert(not characteristics is None)


        env = self.generateEnvironment({'variables':{}})
        state = []
        # most of the internal variables should be fixed, except for
        # long./lat..
        internal = self.generateInternalState({'variables':{}})
        external = self.generateExternalState({'variables':{}})

        # need to ensure that precondition is satisfied
        actions = []
        schemas = self.getSystem().getActionSchemas()

        maxNumActions = characteristics.getMaxNumActionsPerMission()
        for numAction in range(maxNumActions):
            schema = schemas[random.choice(schemas.keys())]
            action = self.generateAction(schema, state)
            actions.append(action)

            # figure out what the next state will look like
            state = NEXT_STATE(schema, action, state)

        missionReturn = mission.Mission(env, internal, external, actions)
        return missionReturn


    def generateExternalState(self, variables):
        return system.ExternalState(variables)


    def generateInternalState(self, variables):
        # this may have to be defined for each system

        return system.InternalState(variables)


    def generateEnvironment(self, variables):
        return system.Environment(variables)


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

        return mission.Action(schema.getName(), params)

class DirectedGenerator(TestSuiteGenerator):
    pass
