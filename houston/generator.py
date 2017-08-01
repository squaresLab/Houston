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
        assert(isinstance(characteristics, TestSuiteCharacteristics))
        assert(not characteristics is None)

        tests = TestSuite()

        while not tests.satisfies(characteristics):
            m = self.__generate_mission(limits)
            tests.add(m)

        return tests 


    def __generate_mission(self, limits):
        """
        Generates a single Mission at random.

        :returns    A randomly-generated Mission instance
        """

        # generate a mission context
        tempMission = {}
        tempMission['environment'] = self.populateInitialState('environment')
        tempMission['internal'] = self.populateInitialState('internal')
        tempMission['external'] = self.populateInitialState('external')
        tempMission['actions'] = []
        actionSchemas = self.__system.getActionSchemas()
        for numAction in range(limits['maxActions']):
            action, schema = random.choice(list(actionSchemas.items()))
        tempMission['actions'].append(self.populateAction(action, schema))

        # generate a mission
        return Mission.fromJSON(tempMission)
         


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


    def populateAction(self, action, schema):
        """
        Populates a given action 

        :param      action       action to populate
        :param      schema       schema of the given action

        :returns a dictionary with randomly generated parameters
        """
        actionParameters = schema.getParameters()
        populatedAction = {action:{}}
        if not actionParameters:
            return populatedAction
        for parameterObject in actionParameters:
            parameter = parameterObject.getType()
            if parameter not in self.__pisf['parameters']:
                exit()
            if len(self.__pisf['parameters'][parameter])>1:
                minVal = self.__pisf['parameters'][parameter]['min']
                maxVal = self.__pisf['parameters'][parameter]['max']
                populatedAction[action][parameter] = random.uniform(minVal, maxVal)
            else:
                randomChoice = random.choice(
                    self.__pisf['parameters'][parameter]["options"])
                populatedAction[action][parameter] = randomChoice
        return populatedAction

class DirectedGenerator(TestSuiteGenerator):
    pass
