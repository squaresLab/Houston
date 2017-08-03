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

    # Would it be better to pass the pisf file as the object is generated or
    # in the generate function?
    def __init__(self, system, pisf):
        """
        Constructs a test suite generator for a given system.

        :param      system          system-under-test
        :param      pisf            JSON file that contains the limitations
                                    and options for parameters and other values
                                    used for initial, external states and 
                                    environment. 
        """
        self.__system = system
        self.__pisf   = pisf


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

        :return A TestSuite object.
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


    def generateMission(self, characteristics):
        """
        Generates a single Mission at random.

        :param  characteristics:    the desired characteristics of the mission\
                                    suite to which this test will belong.

        :returns    A randomly-generated Mission instance
        """
        assert(isinstance(characteristics, mission.MissionSuiteCharacteristics))
        assert(not characteristics is None)

        # generate a mission context
        # TODO: avoid generating JSON -- no type-checking
        env = self.populateInitialState('environment')
        internal = self.populateInitialState('internal')
        external = self.populateInitialState('external')

        actions = []
        schemas = self.__system.getActionSchemas()
        maxNumActions = characteristics.getMaxNumActions()
        for numAction in range(maxNumActions):
            schema = random.choice(schemas)
            action = self.generateAction(schema)
            actions.append(action)

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


    def generateAction(self, schema):
        """
        Generates an action at random

        :param      schema: the schema to which this action belongs, given as\
                            an ActionSchema instance

        :returns    A randomly-generated Action instance
        """
        assert(isinstance(schema, system.ActionSchema) and not schema is None)

        params = {}
        for parameter in schema.getParameters():
            name = parameter.getName()
            params[name] = VALUE

        return mission.Action(schema.getName(), params)
