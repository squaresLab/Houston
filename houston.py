#!/usr/bin/python2.7

# TODO: Description!

import time
import datetime
import json
import os
import sys
import errno
import thread
import signal
import math
import random
import RandomMissionGenerator as RandomMissionGenerator
import ReportAnalyzer         as ReportAnalyzer
import rospy
import xmlrpclib
import argparse


from gazebo_msgs.msg   import ModelStates
from geopy             import distance
from nav_msgs.msg      import Odometry
from geometry_msgs.msg import PoseStamped
from mavros_msgs.msg   import BatteryStatus
from sensor_msgs.msg   import NavSatFix
from mavros_msgs.srv   import CommandLong, SetMode, CommandBool, CommandTOL

HOME_COORDINATES              = (-35.3632607, 149.1652351)
ERROR_LIMIT_DISTANCE          = .3 # 30cm TODO: pick a better name
TIME_INFORM_RATE              = 10 # seconds. How often log time
STABLE_BUFFER_TIME            = 5.0  # Seconds time to wait after each command
ROBOT_MODEL_NAME              = 'iris_demo' # name of the model being used in gazebo
OUTPUT_FOLDER                 = datetime.datetime.now().strftime("%Y-%m-%d_%H:%M:%S")


# Error needs further handling
def error(error, quiet, log_in_file):
    log(error, quiet, log_in_file, 'ERROR')

# Logs..
def log(to_log, quiet, log_in_file, nature = 'LOG'):
    if log_in_file:
        if os.path.exists('houston.log'):
            a_w = 'a' # append if already exists
        else:
            a_w = 'w' # make a new file if not
        with open('houston.log', a_w) as log_file:
            log_file.write('[{}]: {} \n'.format(nature, to_log))
    if not quiet:
        print '[{}]: {}'.format(nature, to_log)


class ROSHandler(object):
    def __init__ (self, target):
        self.mission_info               = None
        # Report gets initialized in monitor
        self.report                     = None
        # mission_on is used to mark if the mission is on going. Monitor updates,
        # mission_on to false if the mission has failed.
        self.mission_on                 = True
        self.initial_set                = [False, False, False, False]
        self.starting_time              = time.time()
        self.target                     = target
        self.battery                    = [0,0]
        self.min_max_height             = [-1,0]
        self.lock_min_height            = True
        self.initial_global_coordinates = [0,0]
        self.initial_model_position     = [0,0,0]
        self.initial_odom_position      = [0,0,0]
        self.current_global_coordinates = [0,0]
        self.current_model_position     = [0,0,0]
        self.current_odom_position      = [0,0,0]
        self.global_alt                 = [0,0]

        # option updated in line 413
        self.quiet                      = False
        self.log_in_file                = True
        # added to hable specific intents (meaning intents to each location or action)
        self.starting_values_current_action = {}
        self.current_action                 = -1
        self.total_distance_traveled        =  0

    # Checks that MAVROS node is running
    def check_mavros(self):
        m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
        code, status_message, uri = m.lookupNode('/mavros', '/mavros')
        return code == 1

    def update_distance_traveled(self, _from, _to):
        distance = euclidean(_from, _to)
        self.total_distance_traveled += distance
        return distance


    # Verifies that the system has reached its correct position by comparing
    # the distance between the current model position and the position where is
    # supposed to be.
    def check_go_to_completion(self, expected_coor, pose, pub):
        position = pose.pose.position
        local_action_time = time.time()
        r = rospy.Rate(10)
        previous_location = get_gazebo_model_positon()
        remaining_distance = euclidean((position.x, position.y), \
            (self.current_model_position[0], self.current_model_position[1]))
        expected_distance = float(remaining_distance)
        local_distance_traveled = 0
        while remaining_distance > ERROR_LIMIT_DISTANCE  and self.mission_on:
            r.sleep()
            pub.publish(pose)

            current_location = get_gazebo_model_positon()
            local_distance_traveled += self.update_distance_traveled((\
                previous_location.x, previous_location.y), (current_location.x, \
                current_location.y))
            previous_location = current_location

            local_action_time = \
                self.timer_log(local_action_time, 2, 'Remaining: {}, Distance traveled: {}'.\
                format(remaining_distance, self.total_distance_traveled)) # TODO
            remaining_distance = euclidean((pose.pose.position.x,pose.pose.position.y), \
                (self.current_model_position[0], self.current_model_position[1]))
        # This is done to double check, that the current position is the actual
        # goal position.
        if remaining_distance > ERROR_LIMIT_DISTANCE:
            return (False, position), 'System did not reached location on time',\
                (expected_distance, local_distance_traveled)
        time.sleep(STABLE_BUFFER_TIME)
        return (True, position), 'System reached location', (expected_distance,\
            local_distance_traveled)

    # Makes sure that the system has landed.
    def check_land_completion(self, alt, wait = STABLE_BUFFER_TIME):
        local_action_time = time.time()
        self.lock_min_height = True
        while self.current_model_position[2] >= ERROR_LIMIT_DISTANCE and \
            self.mission_on:
            local_action_time = self.timer_log(local_action_time, 5, \
            'Waiting to reach land. Goal: ~0 - Current: {}'.format(\
                self.current_model_position[2]))
        if self.current_model_position[2] >= ERROR_LIMIT_DISTANCE:
            return False, 'System did not land on time'
        time.sleep(wait)
        return True, 'System has landed'

    # Makes sure that the system reaches a given altitude (takeoff).
    def check_takeoff_completion(self, alt):
        local_action_time = time.time()

        # We check with current_odom_position beacuse the difference between,
        # the ground truth and the current_odom_position increases as the alt
        # does.
        while alt >= (self.current_odom_position[2] + ERROR_LIMIT_DISTANCE)\
            and self.mission_on:
            local_action_time = self.timer_log(local_action_time, 5, \
                'Waiting to reach alt. Goal: {} - Current: {}'.format(alt, \
                self.current_odom_position[2]))
        if self.min_max_height[0] == -1:
            self.min_max_height[0] = self.current_odom_position[2]
            self.lock_min_height = False


        if alt < (self.current_model_position[2] - ERROR_LIMIT_DISTANCE):
            return (False, alt), 'System did not reach height on time'
        time.sleep(STABLE_BUFFER_TIME)

        return (True, alt), 'System reached height'

    # Sets the system to GUIDED, arms and takesoff to a given altitude.
    # TODO: add mode to mission parameters?
    def ros_command_takeoff(self, alt):
        set_mode = rospy.ServiceProxy('/mavros/set_mode', SetMode)
        res = set_mode(0, "GUIDED")
        if res: # DO check res return to match bool
            log("Mode changed to GUIDED", self.quiet, self.log_in_file) # TODO log
        else:
            error("System mode could not be changed to GUIDED", self.quiet)

        arm = rospy.ServiceProxy('/mavros/cmd/arming', CommandBool)
        # TODO return if arm or mode fail
        if arm(True):
            log("System ARMED...", self.quiet, self.log_in_file)
        else:
            error("System could not be ARMED.", self.quiet, self.log_in_file)

        takeoff = rospy.ServiceProxy('/mavros/cmd/takeoff', CommandTOL)
        if takeoff(0, 0, 0, 0, alt):
            log("System Taking off...", self.quiet, self.log_in_file)
        else:
            error("System did not take off.", self.quiet, self.log_in_file)

        pass_fail, message = self.check_takeoff_completion(alt)
        log(message, self.quiet, self.log_in_file)

        self.report.update_action_output('Takeoff', {'Time': time.time() - self.starting_time,
            'Output': pass_fail})
        return pass_fail

    # Makes a service call to coomand the system to land
    def ros_command_land(self, alt, wait = None):
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        if land(0, 0, 0, 0, alt):
            log("System landing...", self.quiet, self.log_in_file)
        else:
            error("System is not landing.", self.quiet, self.log_in_file)
        pass_fail, message = self.check_land_completion(alt)
        log(message, self.quiet, self.log_in_file)
        self.report.update_action_output('Land', {'Time': time.time() - self.starting_time,
            'Output': pass_fail})
        return pass_fail

    # Gets the current x and y values using latitude and longitud instead of
    # getting the values form local posiiton (odom)
    def get_current_x_y(self):
        x = distance.great_circle(HOME_COORDINATES, ( HOME_COORDINATES[0], \
            self.current_global_coordinates[1],)).meters
        y = distance.great_circle(HOME_COORDINATES, (self.current_global_coordinates[0],\
         HOME_COORDINATES[1],)).meters
        if HOME_COORDINATES[0]> self.current_global_coordinates[0]:
            y = -y
        if HOME_COORDINATES[1]> self.current_global_coordinates[1]:
            x = -x

        return x, y

    # Calculates the expected latitude and longitude, x and y are given in meters.
    def get_expected_lat_long(self, x_y, target, x_distance, y_distance):
        expected_lat  = 0
        expected_long = 0
        if float("{0:.0f}".format(math.fabs(y_distance))) == 0:
            expected_lat = self.initial_global_coordinates[0]
        else:
            if target['y']> x_y[1]:
                expected_lat  = self.initial_global_coordinates[0] + ((y_distance / \
                    6378000.0) * (180.0/math.pi))
            else:
                expected_lat  = self.initial_global_coordinates[0] - ((y_distance / \
                    6378000.0) * (180.0/math.pi))
        if float("{0:.0f}".format(math.fabs(x_distance))) == 0:
            expected_long = self.initial_global_coordinates[1]
        else:
            if target['x']> x_y[0]:
                expected_long = self.initial_global_coordinates[1] + ((x_distance / \
                    6378000.0) * (180.0/math.pi) / math.cos(math.radians(\
                    self.initial_global_coordinates[0])))
            else:
                expected_long = self.initial_global_coordinates[1] - ((x_distance / \
                    6378000.0) * (180.0/math.pi) / math.cos(math.radians(\
                    self.initial_global_coordinates[0])))
        return expected_lat, expected_long

    def get_the_expected_distance_from_lat_long(self, target):
        current_x, current_y = self.get_current_x_y()
        x_y = (current_x, current_y)
        x_distance = target['x'] - current_x - ERROR_LIMIT_DISTANCE
        y_distance = target['y'] - current_y -  ERROR_LIMIT_DISTANCE
        expected_lat, expected_long = self.get_expected_lat_long(x_y, target, \
            x_distance, y_distance)
        expected_coor = (expected_lat, expected_long)
        log('Using coordinates: initial: {} -  expected: {}'.format(\
            self.initial_global_coordinates, expected_coor), self.quiet, \
                self.log_in_file)
        return  distance.great_circle(self.initial_global_coordinates, \
        expected_coor).meters

    # Resets the initial global position
    def reset_initial_global_position(self):
        self.initial_set[1] = False

    # Resets the initail model position
    def reset_intial_model_position(self):
        self.initial_set[0] = False

    # Commands the system to a given location.
    # mptp = multiple point to point mission type.
    def ros_command_go_to(self, target, mptp):
        # It makes sure that the initial position is updated in order to calculate
        # the next coordinate
        if mptp:
            self.reset_initial_global_position()
        go_to_publisher = rospy.Publisher('/mavros/setpoint_position/local',\
            PoseStamped, queue_size=10)
        pose = PoseStamped()
        pose.pose.position.x = float(target['x'])
        pose.pose.position.y = float(target['y'])
        pose.pose.position.z = float(target['z'])
        expected_lat      = None
        expected_long     = None
        expected_coor     = None
        expected_distance = None

        # 0,0 is set to HOME which is the starting position of the system.
        if target['x'] == 0 and target['y'] == 0:
            expected_coor = (HOME_COORDINATES[0], HOME_COORDINATES[1])

            expected_distance = distance.great_circle(self.initial_global_coordinates, \
                expected_coor).meters
            log('Using home coordinates: initial: {} -  expected: {}'.format(\
                self.initial_global_coordinates, expected_coor), self.quiet, \
                    self.log_in_file)
        else:
            expected_distance = self.get_the_expected_distance_from_lat_long(target)

        self.current_global_coordinates = self.initial_global_coordinates
        log('Expected distance to travel : {}'.format(expected_distance), \
            self.quiet, self.log_in_file)


        current_model_position = get_gazebo_model_positon()
        cmp = current_model_position

        pass_fail, message, distance_metrics = self.check_go_to_completion(\
            expected_coor, pose, go_to_publisher)
        log(message, self.quiet, self.log_in_file)


        self.report.update_action_output('GoTo_{}'.format(self.current_action), \
            {'Time': time.time() - self.starting_time,'Output': pass_fail[0], \
            'Goal':{'From':{'x': float(-cmp.y), 'y': float(cmp.x), 'z': float(cmp.z)}, \
                    'To': {'x': float(target['x']), 'y': float(target['y']), 'z': float(target['z']) }}, \
            'DistanceTraveled': \
                    {'Expected': distance_metrics[0],\
                     'Traveled': distance_metrics[1]}})

        return pass_fail

    # Callback for model position sub. It also updates the min and the max height
    def ros_monitor_callback_model_position_gazebo(self, data):
        pose_reality = data.pose[data.name.index(ROBOT_MODEL_NAME)]
        real_position = pose_reality.position

        if not self.initial_set[0]:
            self.initial_model_position[0]        = -real_position.y
            self.initial_model_position[1]        = real_position.x
            self.initial_model_position[2]        = real_position.z
            self.initial_set[0]                   = True
        self.current_model_position[0]            = -real_position.y
        self.current_model_position[1]            = real_position.x
        self.current_model_position[2]            = real_position.z

    # Callback for global position sub
    def ros_monitor_callback_global_position(self, data):
        if not self.initial_set[1]:
            self.initial_global_coordinates[0]    = data.latitude
            self.initial_global_coordinates[1]    = data.longitude
            self.global_alt[0]                    = data.altitude
            self.initial_set[1]                   = True
        self.current_global_coordinates[0]        = data.latitude
        self.current_global_coordinates[1]        = data.longitude
        self.global_alt[1]                        = data.altitude

    # Callback for battery sub
    def ros_monitor_callback_battery(self, data):
        if not self.initial_set[2]:
            self.battery[0]                       = data.remaining
            self.initial_set[2]                   = True
        self.battery[1]                           = data.remaining

    # Callback for local_position sub
    def ros_monitor_callback_odom_local_position(self, data):
        if data.pose.pose.position.z > self.min_max_height[1]:
            self.min_max_height[1] = data.pose.pose.position.z
        if data.pose.pose.position.z < self.min_max_height[0] and not \
            self.lock_min_height:
            self.min_max_height[0] = data.pose.pose.position.z

        if not self.initial_set[3]:
            self.initial_odom_position[0]         = data.pose.pose.position.x
            self.initial_odom_position[1]         = data.pose.pose.position.y
            self.initial_odom_position[2]         = data.pose.pose.position.z
            self.initial_set[3]                   = True
        self.current_odom_position[0]             = data.pose.pose.position.x
        self.current_odom_position[1]             = data.pose.pose.position.y
        self.current_odom_position[2]             = data.pose.pose.position.z

    # Timer which logs information with a given message.
    def timer_log(self, temp_time, time_rate = TIME_INFORM_RATE, message= ''):
        current_time = time.time()
        if  (current_time - temp_time) > time_rate:
            log('Current time: {} : {}'.format((time.time() - self.starting_time),\
                message), self.quiet, self.log_in_file)
            return current_time
        else:
            return temp_time

    # Checks failure flags
    def check_failure_flags(self, failure_flags):
        current_time = time.time() - self.starting_time
        if time.time() - self.starting_time >= float(failure_flags['Time']):
            return True, 'Time exceeded: Expected: {} Current: {}'.format(\
                failure_flags['Time'], current_time)
        # Checks battery
        elif self.battery[0] - self.battery[1] >= float(failure_flags['Battery']):
            return True, 'Battery exceeded: Expected: {} - Current: {} - Time: {}'.\
                format(failure_flags['Battery'], (self.battery[0] - self.battery[1]), \
                current_time)
        # Checks max height
        elif self.min_max_height[1]  >= float(failure_flags['MaxHeight']):
            return True, 'Max height exceeded: Expected: {} - Current: {} - Time: {}'.\
                format(failure_flags['MaxHeight'], self.min_max_height[1], current_time)
        # Checks min height
        elif self.min_max_height[0] != -1 and self.min_max_height[0] <= float(\
            failure_flags['MinHeight']):
            return True, 'Min height exceeded: Expected: {} - Current: {} - Time: {}'.\
                format(failure_flags['MinHeight'], self.min_max_height[0], current_time)
        return False, None

    # Updates quality attributes.
    def get_quality_attributes(self):
        return {'Time': (time.time() - self.starting_time), \
                'Battery': self.battery[0] - self.battery[1], \
                'MinHeight': self.min_max_height[0], \
                'MaxHeight': self.min_max_height[1]}

    # Checks if the current state of the system violates an intent.
    def check_general_intents(self, intents, current_report_data):
        current_time =  time.time() - self.starting_time
        current_battery_used = self.battery[0] - self.battery[1]
        # Checks time
        if current_time >= float(intents['Time']):
            current_report_data['Time'] = {'Time':current_time,'Success':False}
        # Checks Battery
        if current_battery_used >= float(intents['Battery']):
            current_report_data['Battery'] = {'Time':current_time, 'Success':False, \
            'Current-Battery': current_battery_used, 'Intended-Battery': \
                intents['Battery'] }
        # Checks max height
        if self.min_max_height[1] >= float(intents['MaxHeight']):
            current_report_data['MaxHeight'] = {'Time':current_time, 'Success':False, \
            'Current-MaxHeight': self.min_max_height[1], 'Intended-MaxHeight': \
                intents['MaxHeight']}
        # Checks min height
        if not self.lock_min_height and self.min_max_height[0] <= float(intents['MinHeight']):
            current_report_data['MinHeight'] = {'Time':current_time, 'Success':False, \
            'Current-MinHeight': self.min_max_height[0], 'Intended-MinHeight': \
                intents['MinHeight']}
        return current_report_data

    # Checks the intents for a specific portion of the mission.
    def check_specific_intents(self, intents, current_report_data):
        specific_intent_current_time = time.time() - self.starting_values_current_action['Time']
        specific_intent_current_battery = self.starting_values_current_action['Battery'] - self.battery[1]
        # Checks time
        if specific_intent_current_time >= float(intents['Time']):
            current_report_data['Time'] = {'Curremt-Time':specific_intent_current_time, \
                'Intended-Time': intents['Time'],'Success':False}
        # Checks Battery
        if specific_intent_current_battery >= float(intents['Battery']):
            current_report_data['Battery'] = {'Time':specific_intent_current_time, \
                'Success':False, 'Current-Battery': specific_intent_current_battery, \
                'Intended-Battery': intents['Battery'] }
        # Checks max height
        if self.current_odom_position[2] >= float(intents['MaxHeight']):
            current_report_data['MaxHeight'] = {'Time':specific_intent_current_time, \
                'Success':False, 'Current-MaxHeight': self.min_max_height[1], \
                'Intended-MaxHeight': intents['MaxHeight']}
        # Checks min height
        if not self.lock_min_height and self.current_odom_position[2] <= float(intents['MinHeight']):
            current_report_data['MinHeight'] = {'Time':specific_intent_current_time, \
                'Success':False, 'Current-MinHeight': self.current_odom_position[2], \
                'Intended-MinHeight': intents['MinHeight']}
        return current_report_data

    # Starts four subscribers to populate the system's location, system battery and
    # the model position which is very similar to the position given by the local position.
    def start_subscribers(self):
        model_pos_sub   = rospy.Subscriber("/gazebo/model_states", ModelStates, \
            self.ros_monitor_callback_model_position_gazebo, queue_size=10)
        global_pos_sub  = rospy.Subscriber('/mavros/global_position/global', \
            NavSatFix, self.ros_monitor_callback_global_position)
        battery_sub     = rospy.Subscriber('/mavros/battery', BatteryStatus, \
          self.ros_monitor_callback_battery)
        local_odom_sub  = rospy.Subscriber('/mavros/local_position/odom', \
            Odometry, self.ros_monitor_callback_odom_local_position)
        time.sleep(2)

    # Updates intents, quality attributes and checks failure_flags.
    # Sends all the data to the report generator.
    def ros_monitor(self, quality_attributes, intents, failure_flags):
        self.report = Report(self, self.mission_info, len(intents['Specific']))
        self.start_subscribers()

        while self.mission_on:
            fail_g, message  = self.check_failure_flags(failure_flags)
            if fail_g:
                log('Mission Failed. Command to land will start now.', self.quiet, \
                    self.log_in_file)
                self.ros_command_land(1)
                self.mission_on = False
                self.report.update_failure_flag(message)
            self.report.update_quality_attributes_report(self.get_quality_attributes())
            self.report.update_general_intents_report(self.check_general_intents(\
                intents['General'], self.report.get_general_intent_report()))
            if self.current_action != -1:
                self.report.update_specific_intents_report(self.check_specific_intents\
                    (intents['Specific'][self.current_action], \
                    self.report.get_specific_intent_report(self.current_action)), \
                    self.current_action)

    # Sets the mission to over, which would stop all while loops related to the
    # check of a action execution.
    def ros_set_mission_over(self):
        self.mission_on = False

    # Updates the number of the current action. This is used for multiple point
    # to point mission. It allow the program to check for specific intents.
    def ros_update_current_action(self, action):
        self.current_action = action
        self.starting_values_current_action = {}
        self.starting_values_current_action['Time'] = time.time()
        self.starting_values_current_action['Battery'] = self.battery[1]

    # Populates the mission info, quiet, and log in file.
    def ros_set_mission_info(self, mission_info, quiet, log_in_file):
        self.mission_info    = mission_info
        self.quiet           = quiet
        self.log_in_file     = log_in_file

class Report(object):

    def __init__(self, ros_handler, mission_info, number_of_locations):
        self.ros_handler                  = ros_handler
        self.mission_info                 = mission_info
        self.quality_attributes_report    = []
        self.failure_flags_report         = 'Success'
        self.general_intents_report       = {}
        self.specific_intents_report      = [{}]
        self.action_output                = {}
        self.current_time                 = time.time()
        self.total_distance_traveled      = ros_handler.total_distance_traveled
        self.action_output                = None
        for x in range(0, number_of_locations - 1):
            self.specific_intents_report.append({})


    def get_general_intent_report(self):
        return self.general_intents_report

    def get_specific_intent_report(self, current_action):
        return self.specific_intents_report[current_action]

    def update_quality_attributes_report(self, data):
        if (time.time() - self.current_time) >= 2:
            self.quality_attributes_report.append(data)
            self.current_time = time.time()

    def update_general_intents_report(self, intent_report):
        if self.general_intents_report != intent_report:
            self.general_intents_report = intent_report

    def update_specific_intents_report(self, data, current_action):
        if self.specific_intents_report[current_action] != data:
            self.specific_intents_report[current_action] = dict(data)


    def update_failure_flag(self, data):
        self.failure_flags_report = data

    def update_action_output(self, action, output):
        if self.action_output == None:
            self.action_output = {}
        self.action_output[action] = dict(output)

    def get_action_output(self):
        self.action_output['TotalDistanceTraveled'] = self.ros_handler.total_distance_traveled

    # Generates a report in JSON format
    def generate(self):
        data_to_dump = {}
        data_to_dump['MissionType'] = self.mission_info.mission_info['Action']['Type']
        data_to_dump['RobotType'] = self.mission_info.robot_type
        data_to_dump['Map'] = self.mission_info.map
        data_to_dump['LaunchFile'] = self.mission_info.launch_file
        data_to_dump['OverallTime'] = str(time.time() - self.ros_handler.starting_time)
        data_to_dump['TotalDistanceTraveled'] = self.ros_handler.total_distance_traveled
        data_to_dump['QualityAttributes'] = self.quality_attributes_report
        data_to_dump['ActionOutput'] = self.action_output
        data_to_dump['Genral-Intents'] = self.general_intents_report
        data_to_dump['Specific-Intents'] = self.specific_intents_report
        data_to_dump['Failure Flags'] = self.failure_flags_report
        report_present = 0
        report_file = 'outputs/{}/report.json'.format(OUTPUT_FOLDER)
        try:
            report_present = os.stat(report_file).st_size
        except:
            log('No previous report found. Creating a new one', self.ros_handler.quiet, \
            self.ros_handler.log_in_file)
        if report_present == 0:
            report = {'Reports': {'0': data_to_dump}}
            write_json_report(report_file, report)
        else:
            report = open_json_file(report_file)
            report['Reports'][str(len(report['Reports']) )] =  data_to_dump
            write_json_report(report_file, report)



class Mission(object):

    def __init__(self, mission_info):
        self.robot_type         = mission_info['RobotType']
        self.launch_file        = mission_info['LaunchFile']
        self.map                = mission_info['Map']
        self.mission_info       = mission_info['Mission']
        self.missions_supported = ('PTP', 'MPTP', 'Extraction')

    # Checks that everything is the for the mission execution. It also starts,
    # ROSHandler and starts Houston's node
    def initial_check(self):
        if self.mission_info['Action']['Type'] not in self.missions_supported:
            error('Mission: {}. Not supported.'.format(self.mission_info['Action']\
                ['Type']), False, False)
            exit()
        ros = ROSHandler('mavros')
        main = rospy.init_node('HoustonMonitor')
        if not ros.check_mavros():
            error('Missing mavros', False, False)
            sys.exit()
        return ros, main

    # Starts action point to point.
    def execute_point_to_point(self, action_data, ros, action = 0):
        command_success = {}
        command_success['takeoff'] = ros.ros_command_takeoff(action_data['alt'])
        ros.ros_update_current_action(action)
        command_success['go_to'] = (action_data, ros.ros_command_go_to(action_data, False))
        command_success['land'] = ros.ros_command_land(action_data['alt'])
        return command_success

    # Executes multiple point to point action
    def execute_multiple_point_to_point(self, action_data, ros):
        command_success = {}
        command_success['takeoff']= ros.ros_command_takeoff(action_data[0]['alt'])
        location_count = 0
        for target in action_data:
            ros.ros_update_current_action(location_count)
            command_success['go_to_{}'.format(location_count)] = \
                ros.ros_command_go_to(target, True)
            location_count += 1
        command_success['land'] = ros.ros_command_land(action_data[0]['alt'])
        return command_success

    # Executes extraction action
    def execute_extraction(self, action_data, ros):
        initial_x_y = get_gazebo_model_positon()
        to_command_success = self.execute_point_to_point(action_data,ros, 0)
        time.sleep(action_data['wait'])
        action_data['x'] = -initial_x_y.y
        action_data['y'] = initial_x_y.x
        ros.reset_intial_model_position()
        from_command_success = self.execute_point_to_point(action_data, ros, 1)
        return {'to':to_command_success, 'from': from_command_success}

    # Checks that all the required parameters for a correct mission run are present
    def check_parameters(self, parameters):
        gen_parameters = ['Time', 'Battery', 'MaxHeight', 'MinHeight']
        if 'QualityAttributes' in parameters:
            if not all  (param in parameters['QualityAttributes'] for param \
                in gen_parameters):
                error("QualityAttributes description does not have enough attributes")
        else:
            error('QualityAttributes not found.')
        if 'Intents' in parameters:
            if not all (param in parameters['Intents'] for param in gen_parameters):
                error("Intents description does not have enough attributes")
        else:
            error("Intents not found")
        if 'FailureFlags' in parameters:
            if not all (param in parameters['FailureFlags'] \
                for param in gen_parameters):
                error("FailureFlags description does not have enough attributes")
        else:
            error("FailureFlags not found")
        return True

    # Gets the parameters of an action.
    def get_params(self, mission_action, multiple_actions = False):
        params_to_return = {
            'x': None,
            'y': None,
            'z': None,
            'x_d': None,
            'y_d': None,
            'z_d': None,
            'alt': None,
            'wait' : None,
            'Type' : None}
        params_to_return_multiple_case = []
        if multiple_actions:
            for locations in mission_action['Locations']:
                params = {'x': None,'y': None,'z': None,'x_d': None,'y_d': None,\
                'z_d':None,'alt':None,'wait':None,'Type': None} # TODO
                for param in locations:
                    if param == 'Type':
                        continue
                    params[param] = float(locations[param])
                params_to_return_multiple_case.append(params)
            return params_to_return_multiple_case
        else:
            for param in mission_action:
                if param == 'Type':
                    continue
                params_to_return[param] = float(mission_action[param])
            return params_to_return

    # Looks into the type of action and executes them.  Function starts a monitor
    # thread which constantly updates the systems location and data required for the mission.
    def execute(self, quiet, log_in_file):
        ros, main = self.initial_check()
        #self.check_parameters(self.mission_info)
        mission_action     = self.mission_info['Action']
        quality_attributes = self.mission_info['QualityAttributes']
        intents            = self.mission_info['Intents']
        failure_flags      = self.mission_info['FailureFlags']
        success_report     = []
        try:
            ros.ros_set_mission_info(self, quiet, log_in_file)
            thread.start_new_thread(ros.ros_monitor, (quality_attributes, intents, \
                failure_flags))
            if mission_action['Type'] == 'PTP':
                action_data = self.get_params(mission_action)
                success_report.append(self.execute_point_to_point(action_data, ros))
            elif mission_action['Type'] == 'MPTP':
                action_data = self.get_params(mission_action, True)
                success_report.append(self.execute_multiple_point_to_point(action_data, ros))
            elif mission_action['Type'] == 'Extraction':
                action_data = self.get_params(mission_action)
                success_report.append(self.execute_extraction(action_data, ros))
            ros.ros_set_mission_over()
        except KeyboardInterrupt:
            ros.ros_set_mission_over()
            log('User KeyboardInterrupt... exiting.', False, False)
            sys.exit(0)
        except Exception:
            raise
        ros.report.generate()
        print success_report


# Checks that JSON file meets the requirements to start the mission.
def check_json(json_file):
    if not 'MDescription' in json_file:
        error('MDescription')
    elif not 'RobotType' in json_file['MDescription']:
        error('RobotType')
    elif not 'LaunchFile' in json_file['MDescription']:
        error('LaunchFile')
    elif not 'Map' in json_file['MDescription']:
        error('Map')
    elif not 'Mission' in json_file['MDescription']:
        error('Mission')
    elif not 'Name' in json_file['MDescription']['Mission']:
        error('Mission - Name')
    elif not 'Action' in json_file['MDescription']['Mission']:
        error('Mission - Action')
    elif not 'QualityAttributes' in json_file['MDescription']['Mission']:
        error('Mission - QualityAttrubutes')
    elif not 'Intents' in json_file['MDescription']['Mission']:
        error('Mission - Intents')
    elif not 'FailureFlags' in json_file['MDescription']['Mission']:
        error('Mission - FailrueFlags')
    else:
        log('JSON file meets format requirements.', False, False)


# Gets the distance between two points
def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert a != tuple()
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)

# Gets the gazebo model position. This function is here to allow the position be
# passed to the random mission generator without creating a ROSHandler
def get_gazebo_model_positon(from_outside_mission = False):
    if from_outside_mission:
        temporary_node = rospy.init_node('HoustonMonitor')
    model_states = rospy.client.wait_for_message("/gazebo/model_states", \
        ModelStates, timeout=1.0)
    pose_reality = model_states.pose[model_states.name.index(ROBOT_MODEL_NAME)]
    return pose_reality.position


# Starts the actual mission (Test).
def start_test(mission_description, quiet, log_in_file):
    check_json(mission_description)
    mission = Mission(mission_description['MDescription'])
    mission_results = mission.execute(quiet, log_in_file)

# Handles random missions, loops through the quantity of missions wanted and executes,
# them.
def start_random_mission(mission_type, quantity, quiet, log_in_file, save_missions):

    for x in range(0, int(quantity)):
        randomGenerator = RandomMissionGenerator.RandomMissionGenerator('random',\
            get_gazebo_model_positon(True))
        random_mission = randomGenerator.generate_random_mission(mission_type)
        if save_missions:
            write_json_report('outputs/{}/missions/{}.json'.format(OUTPUT_FOLDER, x),\
                random_mission)
        start_test(random_mission, quiet,log_in_file)

def analyze_report(json_file):
    report = open_json_file(json_file)
    report_analyzer = ReportAnalyzer.ReportAnalyzer(report)
    report_analyzer.analyze()


# Recieves a JSON file opens it and starts the test
def start_json_mission(json_file, quiet, log_in_file):
    start_test(open_json_file(json_file), quiet, log_in_file)

def open_json_file(json_file):
    with open(json_file) as file:
        json_file = json.load(file)
    return json_file

def make_parent_dirs(path):
    try:
        os.makedirs(path)
    except OSError as exc:
        if exc.errno == errno.EEXIST and os.path.isdir(path):
            pass
        else: raise

def safe_open(path):
    if '/' in path:
        make_parent_dirs(os.path.dirname(path))
    return open(path, 'w')

def write_json_report(json_file, report_data):
    log('Writting file: {}'.format(json_file), False, False)
    with safe_open(json_file) as file:
        json.dump(report_data, file, sort_keys=True, indent=4, separators=\
        (',', ': '))

def exit_handler(signal, frame):
    log('User interrupted test, exiting...', False, False)
    sys.exit(0)

def main():
    signal.signal(signal.SIGINT, exit_handler)
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers()
    parser.add_argument('--version', action='version', version='0.0.1')
    parser.add_argument('-l', '--log_in_file', action='store_true', \
        required = False)
    parser.add_argument('-q', '--quiet', action='store_true', required=False, \
        default = False)
    parser.add_argument('-s', '--save_missions', action='store_true', required=False,\
        default = False)

    # One random mission, allows to select one mission type with random parameters
    random_mission_parser = subparsers.add_parser('random-mission')
    random_mission_parser.add_argument('mission_type', help='Mission type. For example: \
        PTP - Point to point. MTP - Muliple point to point. EXTR - Extraction.\
        RDM - Random selection (any of PTP, MTP or EXTR)')
    random_mission_parser.add_argument('quantity', help='How many missions you \
        want to be executed')

    random_mission_parser.set_defaults(func = lambda args: \
        start_random_mission(args.mission_type, args.quantity, args.quiet,\
         args.log_in_file, args.save_missions))

    # Gets mission instructions from a json file
    report_analyzer_parser = subparsers.add_parser('analyze-report')
    report_analyzer_parser.add_argument('json_file', help='Please provide a json\
         file with mission report.')
    report_analyzer_parser.set_defaults(func = lambda args: analyze_report(\
        args.json_file))

    json_mission_parser = subparsers.add_parser('json-mission')
    json_mission_parser.add_argument('json_file', help='Please provide a json\
         file with mission instructions.')
    json_mission_parser.set_defaults(func = lambda args: start_json_mission(\
        args.json_file, args.quiet, args.log_in_file))


    args = parser.parse_args()
    if 'func' in vars(args):
        args.func(args)

if __name__ == "__main__":
    main()
