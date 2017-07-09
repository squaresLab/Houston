import unittest
import turtlebot

class TurtleTest(unittest.TestCase):
    def testStraightLine(self):
        system = TurtleBot()
        with self.assertRaises(Error):
            actions = [
                Action("goto",{
                    'x': 5,
                    'y': 5
                })
            ]
            environment = Environment({
                'launch_file': '/catkin_ws/src/turtlebot_simulator/turtlebot_gazebo/launch/robotest.launch',
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
