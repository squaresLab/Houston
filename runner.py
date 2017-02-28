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
#
# Outcomes
#
# | Collision
# | ReachedGoal(time, distance, accuracy, power*) [should record node failures]
# | SystemCrashed
# | PowerExpired
#
import sys
import rospy
import actionlib
import math

from kobuki_msgs.msg import BumperEvent
from gazebo_msgs.msg import ModelStates
from nav_msgs.msg import Odometry
from actionlib_msgs.msg import GoalStatus
from move_base_msgs.msg import MoveBaseAction, MoveBaseGoal
from geometry_msgs.msg import Point, Quaternion

# TODO: should be passed as part of the mission description
MAX_RUN_TIME = 60

# The name of the model for the robot within Gazebo
# TODO: allow command line customisation (so we can use this with other robots)
ROBOT_MODEL_NAME = "mobile_base"

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

class MissionControl(object):
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
        client.wait_for_result(rospy.Duration(MAX_RUN_TIME))

        time_end = rospy.get_time()
        time_elapsed = time_end - time_start

        # did we reach the goal?
        goal_reached = client.get_state() == GoalStatus.SUCCEEDED

        # ensure that we're not still trying to move towards
        # the goal
        if not goal_reached:
            client.cancel_goal()

        return self.assess(goal_reached, time_elapsed)

    def __init__(self, goal):
        assert isinstance(goal, tuple) and len(goal) == 3
        rospy.init_node('mission_controller')
        rospy.loginfo('Launched mission_controller node')
        self.goal_position = Point(goal[0], goal[1], goal[2])
        self.goal_orientation = Quaternion(0.0, 0.0, 0.0, 1.0)
        self.collided = False

if __name__ == "__main__":

    # target co-ordinates
    target_x = float(sys.argv[1])
    target_y = float(sys.argv[2])
    target = (target_x, target_y, 0.0)

    # build the mission
    mission = MissionControl(target)

    # execute!
    print(mission.execute())
