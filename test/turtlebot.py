import unittest
import turtlebot

class TurtleTest(unittest.TestCase):
    def testStraightLine(self):
        system = TurtleBot()
        with self.assertRaises(TypeError):
            actions = [
                Action("goto", (Parameter("x", 5,"x-value"), Parameter("y", 5,"y-value")))
            ]
            environment = Environment({
                'launch_file': 'robotest.launch',
                'launch_parameters': {}
            })
            initialInternalState = InternalState({
                "x": 10.43,
                "y": 0.5,
                "bumper": False, # we could have defaults?
                "cliff": False,
                "orientation": 12.0,
                "battery": 30.0
            })
            initialExternalState = ExternalState({

            })

            system.setUp(Mission(environment, initialInternalState, initialExternalState, actions))
