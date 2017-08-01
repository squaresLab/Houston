import json
import random

MAX_MISSIONS = 20
MAX_ACTIONS  = 20

'''
PISF: Parameter-Initial-State-Format. This is used to bound parameter values.
'''

class TestSuiteGenerator(object):

    def __init__(self, pisf, actionSchemas, fileOutput):
        self.__pisf          = pisf
        self.__actionSchemas = actionSchemas
        self.__fileOutput    = fileOutput

    def generateRandomTest(self):
        tsd = TestSuiteDumper(self.__fileOutput)
        for numMission in range(MAX_MISSIONS):
            tempMission = {}
            tempMission['environment'] = self.populateInitialState('environment')
            tempMission['internal'] = self.populateInitialState('internal')
            tempMission['external'] = self.populateInitialState('external')
            tempMission['actions'] = []
            for numAction in range(MAX_ACTIONS):
                action, schema = random.choice(list(self.__actionSchemas.items()))
                tempMission['actions'].append(self.populateAction(action, schema))
            tsd.appendMission(tempMission)
        tsd.dumpMissionJSON()


    def populateInitialState(self, state):
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
