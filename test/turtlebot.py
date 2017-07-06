import unittest
import turtlebot

class TurtleTest(unittest.TestCase):
    def testStraightLine(self):
        system = TurtleBot()
        with self.assertRaises(Error):
            actions = [
                Action("takeoff", {"altitude": -30})
            ]
            environment = Environment()
            initial = InternalState({
                "x": 10.43,
                "y": 0.5,
                "bumper": False, # we could have defaults?
                "cliff": False,
                "orientation": 12.0,
                "battery": 30.0
            })

            Mission(environment, initial, actions)
