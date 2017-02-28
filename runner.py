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

MAX_RUN_TIME = 60

# The name of the model for the robot within Gazebo
# TODO: allow command line customisation (so we can use this with other robots)
ROBOT_MODEL_NAME = "mobile_base"

# Used to describe an outcome to the mission
class MissionOutcome(object):
    pass

class CollisionOutcome(MissionOutcome):
    pass

class ReachedGoalOutcome(MissionOutcome):
    pass

class TimeExpiredOutcome(MissionOutcome):
    pass

# Handles a reported collision event
def collision_event_handler(event):
    rospy.loginfo('Handling collision event')
    if event.state == 1: # was the bumper pressed?
        rospy.loginfo('We hit something!')

        # now we want to terminate our action and report the outcome

# Measures the Euclidean distance between two sets of co-ordinates, a and b
# TODO: This can be deceptive.
def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert len(a) != []
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)

# Computes and returns the ground truth pose for the robot
def measure_ground_truth_pose():
    rospy.loginfo('Fetching ground truth pose')
    # TODO: what happens if this times out?
    states = rospy.client.wait_for_message("/gazebo/model_states", ModelStates, timeout=1.0)
    entry_num = states.name.index(ROBOT_MODEL_NAME)
    pose = states.pose[entry_num]
    rospy.loginfo('Fetched ground truth pose')
    return pose

# Computes and returns the believed pose for the robot (provided by odometry)
def measure_believed_pose():
    rospy.loginfo('Fetching believed pose information from /odom')
    # TODO: timeout case?
    odom = rospy.client.wait_for_message("odom", Odometry, timeout=1.0)
    rospy.loginfo('Fetched believed pose information from /odom')
    return odom.pose.pose

def move_to_location(tx, ty, tz=0.0):
    # create an actionlib client for our request
    client = actionlib.SimpleActionClient('move_base', MoveBaseAction)

    # watch out for collisions
    rospy.Subscriber('/mobile_base/events/BumperEvent', BumperEvent, collision_event_handler)
    
    # TODO: concurrency dangers
    while not client.wait_for_server(rospy.Duration.from_sec(5.0)):
        rospy.loginfo("Waiting for move_base client action server to initialise")

    # specify the goal of the move_base clienttion
    goal = MoveBaseGoal()
    goal.target_pose.header.frame_id = "map"
    goal.target_pose.header.stamp = rospy.Time.now()
    goal.target_pose.pose.position = Point(tx, ty, tz)
    goal.target_pose.pose.orientation = Quaternion(0.0, 0.0, 0.0, 1.0)
    
    rospy.loginfo('Sending goal information...')

    time_start = rospy.get_time()
    client.send_goal(goal)

    # blocks until result is returned or max run time has expired
    client.wait_for_result(rospy.Duration(MAX_RUN_TIME))

    time_end = rospy.get_time()
    time_elapsed = time_end - time_start

    # did we reach the goal?
    goal_reached = client.get_state() == GoalStatus.SUCCEEDED

    # stop executing the goal!
    if not goal_reached:
        client.cancel_goal()

    # measure the pose delta
    pose_observed = measure_believed_pose()
    pose_reality = measure_ground_truth_pose()
    real_position = pose_reality.position
    believed_position = pose_observed.position

    # measure the Euclidean distance to the goal
    dist = euclidean((real_position.x, real_position.y, real_position.z), \
                     (tx, ty, tz))

    # measure the positional accuracy of the robot
    accuracy = euclidean((believed_position.x, believed_position.y, believed_position.z), \
                         (real_position.x, real_position.y, real_position.z))

    # quality and safety measurements
    rospy.loginfo('-- Elapsed time: {} seconds'.format(time_elapsed))
    rospy.loginfo('-- Distance to goal: {}'.format(dist))
    rospy.loginfo('-- Positional accuracy: {}'.format(accuracy))

    return goal_reached

if __name__ == "__main__":

    # target co-ordinates
    target_x = float(sys.argv[1])
    target_y = float(sys.argv[2])

    rospy.init_node('mission_controller')
    rospy.loginfo('Launched mission_controller node')

    if move_to_location(target_x, target_y):
        rospy.loginfo('SUCCESS: reached target location')
    else:
        rospy.loginfo('FAILURE: failed to reach the target location')
