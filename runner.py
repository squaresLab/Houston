#!/usr/bin/python2.7

# TODO: Description!

import time
import json
import os
import sys
import thread
import math
import random
import RandomMissionGenerator
import rospy
import xmlrpclib

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
QUALITY_ATTRUBUTE_INFORM_RATE = 5  # seconds.
STABLE_BUFFER_TIME            = 5.0  # Seconds time to wait after each command
ROBOT_MODEL_NAME              = 'iris_demo'

def error(error):
    print '[ERROR]: {}'.format(error)

def log(to_log):
    print '[LOG]: {}'.format(to_log)


class ROSHandler(object):
    def __init__ (self, target):
        self.mission_info               = None
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


    def check_mavros(self):
        m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
        code, status_message, uri = m.lookupNode('/mavros', '/mavros')
        return code == 1


    def check_goto_completion(self, expected_coor, pose, pub):
        position = pose.pose.position
        local_action_time = time.time()
        r = rospy.Rate(10)

        remaining_distance = euclidean((position.x, position.y), \
            (self.current_model_position[0], self.current_model_position[1]))
        while remaining_distance > ERROR_LIMIT_DISTANCE  and self.mission_on:
            r.sleep()
            pub.publish(pose)
            local_action_time = self.timer_log(local_action_time, 2, 'Remaining: {}'.format(remaining_distance)) # TODO
            remaining_distance = euclidean((pose.pose.position.x,pose.pose.position.y), \
                (self.current_model_position[0], self.current_model_position[1]))

        # This is done to double check, that the current position is the actual
        # goal position.
        if remaining_distance > ERROR_LIMIT_DISTANCE:
            return (False, position), 'System did not reached location on time'
        time.sleep(STABLE_BUFFER_TIME)
        return (True, position), 'System reached locaiton'

    # Makes sure that the system has landed.
    def check_land_completion(self, alt, wait = STABLE_BUFFER_TIME):
        local_action_time = time.time()
        self.lock_min_height = True
        while self.current_odom_position[2] >= ERROR_LIMIT_DISTANCE and \
            self.mission_on:
            local_action_time = self.timer_log(local_action_time, 5, 'Waiting to reach land. Goal: ~0 - Current: {}'.format(self.current_model_position[2]))
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
            self.current_model_position[2]))
        self.lock_min_height = False
        if self.min_max_height[0] == -1:
            self.min_max_height[0] = self.current_model_position[2]

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
            log("Mode changed to GUIDED") # TODO log
        else:
            error("System mode could not be changed to GUIDED")

        arm = rospy.ServiceProxy('/mavros/cmd/arming', CommandBool)
        # TODO return if arm or mode fail
        if arm(True):
            log("System ARMED...")
        else:
            error("System could not be ARMED.")

        takeoff = rospy.ServiceProxy('/mavros/cmd/takeoff', CommandTOL)
        if takeoff(0, 0, 0, 0, alt):
            log("System Taking off...")
        else:
            error("System did not take off.")

        return_data, message = self.check_takeoff_completion(alt)
        log(message)
        return return_data


    # Makes a service call to coomand the system to land
    def ros_command_land(self, alt, wait = None):
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        if land(0, 0, 0, 0, alt):
            log("System landing...")
        else:
            error("System is not landing.")
        return_data, message = self.check_land_completion(alt)
        log(message)
        return return_data



    # Gets the current x and y values using latitude and longitud instead of
    # getting the values form odom
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


    def reset_initial_global_position(self):
        self.initial_set[0] = False
        self.initial_set[1] = False


    # Commands the system to a given location. Verifies the end of the publications
    # by comparing the current position with the expected position.
    # Need to add z for angular displacement.
    # mptp = multiple point to point mission type.
    def ros_command_goto(self, target, mptp):
        # It makes sure that the initial position is updated in order to calculate
        # the next coordinate
        if mptp:
            self.reset_initial_global_position()
        goto_publisher = rospy.Publisher('/mavros/setpoint_position/local',\
            PoseStamped, queue_size=10)
        pose = PoseStamped()
        pose.pose.position.x = target['x']
        pose.pose.position.y = target['y']
        pose.pose.position.z = target['z']
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
                self.initial_global_coordinates, expected_coor))
        else:
            current_x, current_y = self.get_current_x_y()
            x_y = (current_x, current_y)
            x_distance = target['x'] - current_x - \
                ERROR_LIMIT_DISTANCE
            y_distance = target['y'] -current_y - \
                ERROR_LIMIT_DISTANCE
            expected_lat, expected_long = self.get_expected_lat_long(x_y, target, \
                x_distance, y_distance)
            expected_coor = (expected_lat, expected_long)
            log('Using coordinates: initial: {} -  expected: {}'.format(self.initial_global_coordinates, expected_coor))
            expected_distance = distance.great_circle(self.initial_global_coordinates, \
                expected_coor).meters

        self.current_global_coordinates = self.initial_global_coordinates
        log('Expected distance to travel : {}'.format(expected_distance))

        return_data, message = self.check_goto_completion(expected_coor, pose, \
            goto_publisher)
        log(message)
        return return_data



    # Callback for model position sub. It also updates the min and the max height
    def ros_monitor_callback_model_position_gazebo(self, data):

        pose_reality = data.pose[data.name.index(ROBOT_MODEL_NAME)]
        real_position = pose_reality.position
        if real_position.z > self.min_max_height[1]:
            self.min_max_height[1] = real_position.z
        if real_position.z < self.min_max_height[0] and not \
            self.lock_min_height:
            self.min_max_height[0] = real_position.z

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


    def ros_monitor_callback_battery(self, data):
        if not self.initial_set[2]:
            self.battery[0]                       = data.remaining
            self.initial_set[2]                   = True
        self.battery[1]                           = data.remaining


    def ros_monitor_callback_odom_local_position(self, data):
        if not self.initial_set[3]:
            self.initial_odom_position[0]         = data.pose.pose.position.x
            self.initial_odom_position[1]         = data.pose.pose.position.y
            self.initial_odom_position[2]         = data.pose.pose.position.z
            self.initial_set[3]                   = True
        self.current_odom_position[0]             = data.pose.pose.position.x
        self.current_odom_position[1]             = data.pose.pose.position.y
        self.current_odom_position[2]             = data.pose.pose.position.z



    def timer_log(self, temp_time, time_rate = TIME_INFORM_RATE, message = ''):
        current_time = time.time()
        if  (current_time - temp_time) > time_rate:
            log('Current time: {} : {}'.format((time.time() - self.starting_time), message))
            return current_time
        else:
            return temp_time


    def check_failure_flags(self, failure_flags):
        if time.time() - self.starting_time >= float(failure_flags['Time']):
            return True, 'Time exceeded: Expected: {} Current: {}'.format(failure_flags['Time'], (time.time() - self.starting_time))
        elif self.battery[0] - self.battery[1] >= float(failure_flags['Battery']):
            return True, 'Battery exceeded'
        elif self.current_model_position[2] >= failure_flags['MaxHeight']:
            return True, 'Max Height exceeded'
        else:
            return False, None
        # TODO Min Height

    def check_quality_attributes(self, quality_attributes, current_data, _time):
        if time.time() - _time >= float(quality_attributes['ReportRate']):
            current_data.append({'Time': (time.time() - self.starting_time), \
                'Battery': self.battery[0]-self.battery[1], 'MinHeight': \
                self.min_max_height[0], 'MaxHeight': self.min_max_height[1]})
            return time.time(), current_data
        else:
            return _time, current_data


    def check_intents(self, intents, current_data):
        current_time =  time.time() - self.starting_time
        current_battery_used = self.battery[0] - self.battery[1]
        if current_time >= float(intents['Time']):
            current_data['Time'] = {'Time':current_time,'Success':False}
        if current_battery_used >= float(intents['Battery']):
            current_data['Battery'] = {'Time':current_time, 'Success':False, \
            'Battery': current_battery_used }
        if self.min_max_height[0] >= intents['MaxHeight']:
            current_data['MaxHeight'] = {'Time':current_time, 'Success':False, \
            'MaxHeight': self.current_model_position[2]}
        if self.min_max_height[1]<= intents['MinHeight']:
            current_data['MinHeight'] = {'Time':current_time, 'Success':False, \
            'MinHeight': self.current_model_position[2]}
        return current_data
        # TODO Better name for current_data


    # Starts two subscribers to populate the system's location. It also ensures
    # failure flags. *More to be added
    def ros_monitor(self, quality_attributes, intents, failure_flags, random = False):
        model_pos_sub   = rospy.Subscriber("/gazebo/model_states", ModelStates, \
            self.ros_monitor_callback_model_position_gazebo, queue_size=10)
        global_pos_sub  = rospy.Subscriber('/mavros/global_position/global', \
            NavSatFix \
         , self.ros_monitor_callback_global_position)
        battery_sub     = rospy.Subscriber('/mavros/battery', BatteryStatus, \
          self.ros_monitor_callback_battery)
        local_odom_sub  = rospy.Subscriber('/mavros/local_position/odom', \
            Odometry, self.ros_monitor_callback_odom_local_position)
        time.sleep(2)
        if random:
            return (self.initial_odom_position[0],self.initial_odom_position[1])

        intents_for_report ={
                'Time': True,
                'Battery': True,
                'MaxHeight':True,
                'MinHeight': True}
        report_data = {'QualityAttributes':[],'Intents':intents_for_report,\
        'FailureFlags':'None'}
        temp_time   = time.time() #time used for failure flags and time inform (seconds)
        qua_time    = time.time() #time used for the rate of attribute reports (seconds)
        while self.mission_on:
            temp_time = self.timer_log(temp_time)
            fail, reason = self.check_failure_flags(failure_flags)
            if fail:
                report_data['FailureFlags'] = reason
                self.mission_on = False
                error(reason)
            else:
                qua_time, qua_report = self.check_quality_attributes(\
                    quality_attributes,report_data['QualityAttributes'], qua_time)
                report_data['QualityAttributes'] = qua_report
                report_data['Intents'] = self.check_intents(intents, \
                    report_data['Intents'])

        report_generator = Report(self, report_data, self.mission_info)
        report_generator.generate()


    def ros_set_mission_over(self):
        self.mission_on = False


    def ros_set_mission_info(self, mission_info):
        self.mission_info = mission_info


class Report(object):


    def __init__(self, ros_handler ,report_data, mission_info):
        self.report_data      = report_data
        self.ros_handler = ros_handler
        self.mission_info     = mission_info


    def generate(self):
        data_to_dump = {}
        data_to_dump['MissionType'] = self.mission_info.mission_info['Action']['Type']
        data_to_dump['RobotType'] = self.mission_info.robot_type
        data_to_dump['Map'] = self.mission_info.map
        data_to_dump['LaunchFile'] = self.mission_info.launch_file
        data_to_dump['OverallTime'] = str(time.time() - self.ros_handler.starting_time)
        data_to_dump['QualityAttributes'] = self.report_data['QualityAttributes']
        data_to_dump['Intents'] = self.report_data['Intents']
        data_to_dump['Failure Flags'] = self.report_data['FailureFlags']

        with open('report.json', 'w') as file:
            json.dump(data_to_dump, file)


class Mission(object):

    def initial_check(self):
        ros = ROSHandler('mavros')
        main = rospy.init_node('HoustonMonitor')
        if not ros.check_mavros():
            error('Missing mavros')
            sys.exit()
        return ros, main


    # Starts mission point to point. Function starts a monitor thread which constantly
    # updates the systems location and data required for the mission.
    def execute_point_to_point(self, action_data, ros):
        command_success = {}
        command_success['takeoff'] = ros.ros_command_takeoff(action_data['alt'])
        command_success['go_to'] = (action_data, ros.ros_command_goto(action_data, False))
        command_success['land'] = ros.ros_command_land(action_data['alt'])
        return command_success



    def execute_multiple_point_to_point(self, action_data, ros):
        command_success = {}
        command_success['takeoff']= ros.ros_command_takeoff(action_data[0]['alt'])
        location_count = 0
        for target in action_data:
            command_success['go_to_{}'.format(location_count)] = \
                ros.ros_command_goto(target, True)
            location_count += 1
        command_success['land'] = ros.ros_command_land(action_data[0]['alt'])
        return command_success


    def execute_extraction(self, action_data, ros):
        initial_x_y = ros.current_model_position
        to_command_success = self.execute_point_to_point(action_data['alt'], action_data,False)
        time.sleep(action_data['wait'])
        action_data['x'] = initial_x_y[0]
        action_data['y'] = initial_x_y[1]
        from_command_success = self.execute_point_to_point(action_data['alt'], action_data, False)
        return {'to':to_command_success, 'from': from_command_success}


    # Checks that all the required parameters for a correct mission run are present
    def check_parameters(self, parameters):
        gen_parameters = {'Time', 'Battery', 'MaxHeight', 'MinHeight'}
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


    # Executes mission
    def execute(self):
        ros, main = self.initial_check()
        self.check_parameters(self.mission_info)
        mission_action     = self.mission_info['Action']
        quality_attributes = self.mission_info['QualityAttributes']
        intents            = self.mission_info['Intents']
        failure_flags      = self.mission_info['FailureFlags']
        success_report     = []
        try:
            ros.ros_set_mission_info(self)
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
            else:
                print 'Mission type found not supported'
        except KeyboardInterrupt:
            log('User KeyboardInterrupt... exiting.')
        except Exception:
            raise
        print success_report
        ros.ros_set_mission_over
        sys.exit(0)


    def __init__(self, mission_info):
        self.robot_type  = mission_info['RobotType']
        self.launch_file = mission_info['LaunchFile']
        self.map         = mission_info['Map']
        self.mission_info = mission_info['Mission']


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
        print log('JSON file meets format requirements.')


def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert a != tuple()
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print ('Please provide a mission description file. (JSON)')
        randomGenerator = RandomMissionGenerator()
        json_file = randomGenerator.generateRandomjson()
    with open(sys.argv[1]) as file:
        json_file = json.load(file)
    check_json(json_file)
    mission = Mission(json_file['MDescription'])
    mission_results = mission.execute()
