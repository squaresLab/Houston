import unittest

class ArduTest(unittest.TestCase):
    def testNegativeAltitude(self):
        system = ArduPilot()
        actions = [
            Action("takeoff", {"altitude": -30})
        ]
        mission = Mission(actions)


