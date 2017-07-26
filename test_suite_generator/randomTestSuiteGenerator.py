import testSuiteDumper
import random

#KNOWN Floats
FTYPES = {
    'altitude' : (0.3, 30.0),
    'latitude' : (-90.0, 90.0),
    'longitude': (-180.0, 180.0)
}
STRTYPES = {
    'mode'     : ('GUIDED', 'LOITER', 'RTL')
}

class RandomTestSuiteGenerator(object):
    def __init__(self):
        pass

    def generateRandomTestSuite(self, actionsFormat, maxMissions, maxActions):
        testSuiteDumper2 = testSuiteDumper.TestSuiteDumper('RandomTestSuite_maxm_{}_maxa_{}'.format(maxMissions,maxActions))

        for x in range(maxMissions):
            tempMission = []
            for y in range(random.randint(1, maxActions)):
                kind, params = random.choice(list(actionsFormat.items()))
                tempMission.append({kind: self.populateParameters(params)})
            testSuiteDumper2.appendMission(tempMission)

        testSuiteDumper2.dumpMissionJSON()

    def populateParameters(self, paramsInput):
        params = dict(paramsInput)
        for parameter in params:
            if parameter in FTYPES:
                params[parameter] = random.uniform(FTYPES[parameter][0],
                    FTYPES[parameter][1])
                continue
            if parameter in STRTYPES:
                params[parameter] = random.choice(STRTYPES[parameter])

        return params
