#!/usr/bin/python2.7
#
# Based on code by Miguel Velez:
# https://github.com/miguelvelezmj25/turtlebot-monitoring-infrastructure/blob/develop/src/cp1_gazebo/instructions/localization/map_navigation.py
#
# Provided we trust the bump sensors, we can subscribe to /mobile_base/events/bumper
# to be informed of any bumps. For now, let's go ahead and trust this (then work
# on a better, more general solution for cases where we don't trust the bump
# sensor OR where the bump sensor is inadequate).
#
# * subscribe to bumper event topic
# * terminate test as soon as we collide
#
# Outcomes
#
# | Collision
# | ReachedGoal(time, distance, accuracy, power*) [should record node failures]
# | SystemCrashed
# | PowerExpired
#
import signal
import os
import time
import sys
import rospy
import actionlib
import math
import subprocess
import roslaunch

import xml.etree.ElementTree as ET

from tempfile import NamedTemporaryFile
from kobuki_msgs.msg import BumperEvent
from gazebo_msgs.msg import ModelStates
from nav_msgs.msg import Odometry
from actionlib_msgs.msg import GoalStatus
from move_base_msgs.msg import MoveBaseAction, MoveBaseGoal
from geometry_msgs.msg import Point, Quaternion

# The name of the model for the robot within Gazebo
# TODO: allow command line customisation (so we can use this with other robots)
ROBOT_MODEL_NAME = "mobile_base"

# Used to construct a temporary launch file to pass along launch-time
# parameters to ROSLaunchParent (since there isn't a native way to supply
# parameters).
class EphemeralLaunchFile(object):

    def __init__(self, base_file, parameters):
        # load the contents of the base file
        tree = ET.ElementTree()
        tree.parse(base_file)
        root = tree.getroot()

        # find the corresponding argument for each parameter
        new_parameters = []
        for (param, value) in parameters.items():
            found = False

            # doesn't look at child arguments --- considered unnecessary
            for arg in root.find("arg[@name='{}']".format(param)):
                arg.attrib.pop('default')
                arg.set('value', value)
                found = True

            # if we didn't find the tag for this argument, add a new one
            if not found:
                arg = ET.SubElement(root, 'arg')
                arg.set('name', param)
                arg.set('value', value)

        # write the modified XML to a temporary file
        # n.b. Python will take care of destroying the temporary file during
        # garbage collection
        self.handle = NamedTemporaryFile(suffix='.launch')
        tree.write(self.path())

    def path(self):
        return self.handle.name

# Used to describe an outcome to the mission
class MissionOutcome(object):
    pass


class CollisionOutcome(MissionOutcome):
    def __str__(self):
        return "Collision()"


class GoalReachedOutcome(MissionOutcome):
    def __init__(self, time, distance, pos_error):
        self.time = time
        self.distance = distance
        self.pos_error = pos_error

    def __str__(self):
        return "ReachedGoal(Time = {}, Distance = {}, Pos. Error = {})".format(self.time, self.distance, self.pos_error)


class TimeExpiredOutcome(MissionOutcome):
    def __init__(self, distance, pos_error):
        self.distance = distance
        self.pos_error = pos_error 

    def __str__(self):
        return "TimeExpired(Distance = {}, Pos. Error = {})".format(self.distance, self.pos_error)


# Measures the Euclidean distance between two sets of co-ordinates, a and b
# TODO: This can be deceptive.
def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert len(a) != []
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)

# For now, the only mission involves moving the robot from the spawn-point to
# a given location.
class MissionControl(object):

    # Records any collisions registered via the bumper sensors
    def bumper_listener(self, event):
        if event.state == 1:
            rospy.loginfo('BUMPER: We hit something!')
            self.collided = True


    # Determines the outcome of the mission
    def assess(self, goal_reached, time_elapsed):
        
        # TODO: may be better to terminate straightaway?
        # did we collide at some point?
        if self.collided:
            return CollidedOutcome()

        # determine ground truth position of the robot
        # TODO: what happens if this times out?
        model_states = \
            rospy.client.wait_for_message("/gazebo/model_states", ModelStates, timeout=1.0)
        pose_reality = model_states.pose[model_states.name.index(ROBOT_MODEL_NAME)]
        real_position = pose_reality.position

        # determine the believed position of the robot
        # TODO: timeout case?
        odom = rospy.client.wait_for_message("odom", Odometry, timeout=1.0)
        pose_observed = odom.pose.pose
        believed_position = pose_observed.position

        # measure the Euclidean distance to the goal
        dist = euclidean((real_position.x, real_position.y, real_position.z), \
                         (self.goal_position.x, self.goal_position.y, self.goal_position.z))

        # measure the positional error of the robot
        pos_error = euclidean((believed_position.x, believed_position.y, believed_position.z), \
                              (real_position.x, real_position.y, real_position.z))

        if goal_reached:
            return GoalReachedOutcome(time_elapsed, dist, pos_error)
        else:
            return TimeExpiredOutcome(dist, pos_error)


    # Executes the mission and returns the outcome as a MissionOutcome
    # instance
    def execute(self):
        launch = None
        try:
            # generate an ephemeral launch file to pass the parameters
            ephemeral_launch = EphemeralLaunchFile( self.launch_file, \
                                                    self.launch_parameters)

            # launch ROS
            uuid = roslaunch.rlutil.get_or_generate_uuid(None, False)
            roslaunch.configure_logging(uuid)
            launch_files = [ephemeral_launch.path()]
            launch = roslaunch.parent.ROSLaunchParent(uuid, launch_files, is_core=True)
            launch.start()

            # setup mission controller
            rospy.init_node('mission_controller')
            rospy.loginfo('Launched mission_controller node')
            rospy.Subscriber('/mobile_base/events/bumper', BumperEvent, \
                             self.bumper_listener, callback_args=[self])
            client = actionlib.SimpleActionClient('move_base', MoveBaseAction)

            # TODO: concurrency dangers?
            while not client.wait_for_server(rospy.Duration.from_sec(5.0)):
                rospy.loginfo("Waiting for move_base client action server to initialise")

            # specify the goal for move_base
            goal = MoveBaseGoal()
            goal.target_pose.header.frame_id = "map"
            goal.target_pose.header.stamp = rospy.Time.now()
            goal.target_pose.pose.position = self.goal_position
            goal.target_pose.pose.orientation = self.goal_orientation

            rospy.loginfo('Sending goal information...')
            time_start = rospy.get_time()
            client.send_goal(goal)

            # wait until goal is reached or max time is expired
            client.wait_for_result(rospy.Duration(self.time_limit))

            time_end = rospy.get_time()
            time_elapsed = time_end - time_start

            # did we reach the goal?
            goal_reached = client.get_state() == GoalStatus.SUCCEEDED

            # ensure that we're not still trying to move towards
            # the goal
            if not goal_reached:
                client.cancel_goal()

            return self.assess(goal_reached, time_elapsed)

        # ensure ROS is cleanly exited
        finally:
            if launch:
                launch.shutdown()


    def __init__(self, time_limit, goal, launch_file, parameters):
        assert isinstance(goal, tuple) and len(goal) == 3
        assert time_limit > 0
        self.time_limit = time_limit
        self.goal_position = Point(goal[0], goal[1], goal[2])
        self.goal_orientation = Quaternion(0.0, 0.0, 0.0, 1.0)
        self.launch_file = launch_file
        self.launch_parameters = parameters
        self.collided = False


if __name__ == "__main__":
    # target co-ordinates
    target_x = float(sys.argv[1])
    target_y = float(sys.argv[2])
    target = (target_x, target_y, 0.0)

    # build the mission
    configuration = "/catkin_ws/src/turtlebot_simulator/turtlebot_gazebo/launch/robotest.launch"
    mission = MissionControl(60, target, configuration, {'gui': 'false'})

    # execute!
    print(mission.execute())
