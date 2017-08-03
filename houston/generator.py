import random
import mission

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
        assert(isinstance(characteristics, mission.MissionSuiteCharacteristics))
        assert(not characteristics is None)

        missions = MissionSuite()
        while not missions.satisfies(characteristics):
            m = self.generateMission(characteristics)
            missions.add(m)

        return missions


    def generateMission(self, stateBefore, characteristics):
        """
        Generates a single Mission at random.

        :param  characteristics:    the desired characteristics of the mission\
                                    suite to which this test will belong.

        :returns    A randomly-generated Mission instance
        """
        assert(isinstance(characteristics, mission.MissionSuiteCharacteristics))
        assert(not characteristics is None)

        # generate a mission context
        env = self.populateInitialState('environment')
        internal = self.populateInitialState('internal')
        external = self.populateInitialState('external')

        # generate a state object
        state = PUT_EVERYTHING_TOGETHER()

        # need to ensure that precondition is satisfied

        actions = []
        schemas = self.__system.getActionSchemas()
        maxNumActions = characteristics.getMaxNumActions()
        for numAction in range(maxNumActions):
            schema = random.choice(schemas)
            action = self.generateAction(schema, state)
            actions.append(action)

            # figure out what the next state will look like
            state = NEXT_STATE(schema, action, state)

        mission = mission.Mission(env, internal, external, actions)
        return mission


    def populateInitialState(self, state):
        """
        Populates a given initial state

        :param      state       state to populate

        :returns a dictionary with randomly generated values
        """
        initialState = {'variables': {}}
        PISFState = self.__pisf[state]
        if not PISFState:
            return initialState

        for variable in PISFState:
            if len(PISFState[variable]) > 1:
                minVal = PISFState[variable]['min']
                maxVal = PISFState[variable]['max']
                initialState['variables'][variable] = random.uniform(minVal, maxVal)
            else:

                randomChoice = random.choice(PISFState[variable])
                initialState['variables'][variable] = randomChoice

        return initialState


    def generateInternalState(self):
        pass


    def generateEnvironment(self):
    
        return Environment()


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
