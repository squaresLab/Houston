import unittest
import turtlebot

class TurtleTest(unittest.TestCase):
    def testStraightLine(self):
        system = TurtleBot()
        with self.assertRaises(Error):
            actions = [
                Action("goto", [Parameter("x", 5,"x-value"), Parameter("y", 5,"y-value")])
            ]
            environment = Environment({}, lambda: turtlebot.launch("/catkin_ws/src/turtlebot_simulator/turtlebot_gazebo/launch/robotest.launch". {})) #TODO change directory
            initial = InternalState({
                "x": 10.43,
                "y": 0.5,
                "bumper": False, # we could have defaults?
                "cliff": False,
                "orientation": 12.0,
                "battery": 30.0
            })

            system.setUp(Mission(environment, initial, actions))
