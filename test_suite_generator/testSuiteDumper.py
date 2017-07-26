import json
import os


class TestSuiteDumper(object):
    def __init__(self, testSuiteName):
        self.testSuiteName = testSuiteName
        self.missions      = []

    def appendMission(self, missionInput):
        if len(self.missions) == 0:
            self.missions.append({0:missionInput})
        else:
            self.missions.append({len(self.missions): missionInput})

    def dumpMissionJSON(self):
        with open('{}.json'.format(self.testSuiteName), 'w') as file:
            json.dump({'testSuite': self.missions}, file, sort_keys=True,
                indent=4, separators=(',', ': '))
