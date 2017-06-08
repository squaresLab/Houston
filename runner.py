#!/usr/bin/python2.7

# TODO: Description!

import time
import json
import sys
import rospy
import math
import thread
from geopy.distance import vincenty

from nav_msgs.msg import Odometry
from geometry_msgs.msg import PoseStamped
from mavros_msgs.msg import BatteryStatus
from sensor_msgs.msg import NavSatFix
from mavros_msgs.srv import CommandLong, SetMode, CommandBool, CommandTOL


# Command IDs in MAVLINK
#COMMANDS = {"TAKEOFF": 24, "SETMODE": 176, "ARM": 400 }
#home coordinates
HOME_COORDINATES              = (-35.3632607, 149.1652351) 
ERROR_LIMIT_DISTANCE          = .3 # 30cm TODO: pick a better name 
TIME_INFORM_RATE              = 10 # seconds. How often log time
QUALITY_ATTRUBUTE_INFORM_RATE = 5  # seconds. 



class Error(object):

    def __init__(self, error):
        self.error = error
    
    def format_error(self):
        print '[FORMAT ERROR] JSON file is not properly formated. ('+\
        self.error+')'
        exit()

    def thread_error(self):
        print '[THREAD ERROR] '+ self.error
        exit()
    def failure_flag(self):
        print '[FAILURE FLAG] '
        exit()


class Log(object):

    def __init__(self, log):
        print "[LOG]: " + log


class ROSHandler(object):
    def __init__ (self, target):
        self.mission_on                 = True
        self.initial_set                = [False, False, False]
        self.starting_time              = time.time()
        self.target                     = target
        self.battery                    = [0,0]
        self.min_max_height             = [0,0]
        self.lock_min_max_height        = False

        self.initial_global_coordinates = [0,0]
        self.initial_local_position     = [0,0,0]

        self.current_global_coordinates = [0,0]
        self.current_local_position     = [0,0,0]

        self.global_alt                 = [0,0]
        
    def check_command_completion(self, _type, alt, expected_coor, pose, pub):
        local_action_time = time.time()

        if _type == 'takeoff':
            while ((alt+(ERROR_LIMIT_DISTANCE/2)) >= self.current_local_position[2]) \
            and (self.current_local_position[2] <= (alt-(ERROR_LIMIT_DISTANCE/2))):

                local_action_time = self.inform_time(local_action_time, 5, \
                    'Waiting to reach alt. Goal: '+ str(alt) +' - Current: '\
                    +str(self.current_local_position[2]))
        elif _type == 'land':
            while self.current_local_position[2] >= ERROR_LIMIT_DISTANCE:
                local_action_time = self.inform_time(local_action_time, 5, \
                    'Waiting to reach land. Goal: ~0' +' - Current: '\
                    +str(self.current_local_position[2]))
        elif _type == 'pos':

            self.lock_min_max_height = True
            while vincenty(expected_coor, self.current_global_coordinates).meters\
             >= ERROR_LIMIT_DISTANCE: 

                distance_traveled = vincenty(self.initial_global_coordinates, \
                    self.current_global_coordinates).meters
                pub.publish(pose)
                local_action_time = self.inform_time(local_action_time, 2,\
                 'Distance traveled: ' + str(distance_traveled))
            self.lock_min_max_height = False



    # Sets the system to GUIDED, arms and takesoff to a given altitude.
    # TODO: add mode to mission parameters? 
    def ros_command_takeoff(self, alt):
        set_mode = rospy.ServiceProxy('/mavros/set_mode', SetMode)
        res = set_mode(0, "GUIDED")

        if res: # DO check res return to match bool 
            Log("Mode changed to GUIDED")
        else:
            Error("System mode could not be changed to GUIDED")

        arm = rospy.ServiceProxy('/mavros/cmd/arming', CommandBool)
        res = arm(True)
        if res:
            Log("System ARMED...")
        else:
            Error("System could not be ARMED.")

        takeoff = rospy.ServiceProxy('/mavros/cmd/takeoff', CommandTOL)
        res = takeoff(0, 0, 0, 0, alt)
        if res:
            Log("System Taking off...")
        else:
            Error("System did not take off.")
        self.check_command_completion('takeoff', alt, None, None, None)
        Log('System reached height')
        
        
    #def goto_command(self, lat, longitud):

    # Makes a service call to coomand the system to land
    def ros_command_land(self, alt, last_command):
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        res = land(0, 0, 0, 0, alt)
        if res:
            Log("System landing...")
        else:
            Error("System is not landing.")
        self.check_command_completion('land', None, None, None, None)
        Log('System has landed')


    # Commands the system to a given location. Verifies the end of the publications
    # by comparing the current position with the expected position.
    # Need to add z for angular displacement. 
    def ros_command_goto(self, target):
        goto_publisher = rospy.Publisher('/mavros/setpoint_position/local',\
         PoseStamped, queue_size=10)
        pose = PoseStamped()
        pose.pose.position.x = target[0]
        pose.pose.position.y = target[1]
        pose.pose.position.z = target[2]
        current_coor = (self.current_global_coordinates[0], \
            self.current_global_coordinates[1])
        expected_lat      = None
        expected_long     = None
        expected_coor     = None
        expected_distance = None

        # 0,0 is to HOME which is the starting position of the system. 
        if target[0] == 0 and target[1] == 0:
            expected_coor = (HOME_COORDINATES[0], HOME_COORDINATES[1])
            expected_distance = vincenty(self.initial_global_coordinates, expected_coor).meters
        else:
            # Check for a better solution 
            # TODO: acount for 0 latitude  (x value)
            expected_lat = self.current_global_coordinates[0] + (target[0] * \
                0.000008983)
            expected_long = self.current_global_coordinates[1] + ((target[0] *\
             0.000008983)/ \
                math.cos(self.current_global_coordinates[0] * 0.018))
            expected_coor = (expected_lat, expected_long)
            expected_distance = vincenty(self.current_global_coordinates, expected_coor).meters

        distance_traveled = vincenty(self.initial_global_coordinates, current_coor).meters

        local_action_time = time.time()
        Log('Expected distance to travel: ' + str(expected_distance))
        self.check_command_completion('pos', None, expected_coor, pose, goto_publisher)
        Log('Position reached')

    # Callback for local position sub. It also updates the min and the max height
    def ros_monitor_callback_local_position(self, data):
        if data.pose.position.z > self.min_max_height[1] and not \
            self.lock_min_max_height:
            self.min_max_height[1] = data.pose.position.z
        if data.pose.position.z < self.min_max_height[0] and not \
            self.lock_min_max_height:
            self.min_max_height[0] = data.pose.position.z

        if not self.initial_set[0]:
            self.initial_local_position[0]        = data.pose.position.x
            self.initial_local_position[1]        = data.pose.position.y
            self.initial_local_position[2]        = data.pose.position.z
            self.initial_set[0]                   = True
        self.current_local_position[0]            = data.pose.position.x
        self.current_local_position[1]            = data.pose.position.y
        self.current_local_position[2]            = data.pose.position.z
        

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


    def inform_time(self, temp_time, time_rate = TIME_INFORM_RATE , \
            message = ''):
        current_time = time.time()
        if  (current_time - temp_time) > time_rate:
                Log('Current time: ' + str(time.time() - self.starting_time)+ \
                    ': '+ str(message))
                return current_time
        else:
            return temp_time

    def check_failure_flags(self, failure_flags):
        if time.time() - self.starting_time >= failure_flags['Time']:
            return True, 'Time exceeded'
        elif self.battery[0] - self.battery[1] >= failure_flags['Battery']:
            return True, 'Battery exceeded'
        elif self.current_local_position[2] >= failure_flags['MaxHeight']:
            return True, 'Max Height exceeded'
        else:
            return False, None

    def check_quality_attributes(self, quality_attributes, current_data, _time):
        if time.time() - _time >= float(quality_attributes['ReportRate']):
            current_data.append({'Time': time.time() - self.starting_time, \
                'Battery': self.battery[0]-self.battery[1], 'MinHeight': \
                self.min_max_height[0], 'MaxHeight': self.min_max_height[1]})
            return time.time(), current_data
        else:
            return _time, current_data

    # Starts two subscribers to populate the system's location. It also ensures 
    # failure flags. *More to be added 
    def ros_monitor(self, quality_attributes, intents, failure_flags):        
        local_pos_sub   = rospy.Subscriber('/mavros/local_position/pose', \
            PoseStamped \
         , self.ros_monitor_callback_local_position)
        global_pos_sub  = rospy.Subscriber('/mavros/global_position/global', \
            NavSatFix \
         , self.ros_monitor_callback_global_position)
        battery_sub     = rospy.Subscriber('/mavros/battery', BatteryStatus, \
          self.ros_monitor_callback_battery)
        
        report_data = {'QualityAttributes':[],'FailureFlags':None}
        temp_time   = time.time() #time used for failure flags and time inform
        qua_time    = time.time() #time used for the rate of attribute reports
        while not rospy.is_shutdown():
            temp_time = self.inform_time(temp_time)
            fail, reason = self.check_failure_flags(failure_flags)
            if fail:
                report_data['FailureFlags'] = reason
            else:
                qua_time, qua_report = self.check_quality_attributes(quality_attributes,report_data['QualityAttributes'], qua_time)
                report_data['QualityAttributes'] = qua_report

        report_generator = Report(self, report_data)
        report_generator.generate()

class Report(object):
    def __init__(self, ros_handler_self ,report_data):
        self.report_data      = report_data
        self.ros_handler_self = ros_handler_self

    def generate(self):
        print self.report_data['QualityAttributes']
        print self.report_data['FailureFlags']

#    def check_intents(self, intents):
#       current_data = intents
#        inequality_simbols = {'time':intents['Time'].split(':')[0], 'battery':intents['Battery'].split(':')[0]}
#        values = {'time':intents['Time'].split(':')[1], 'battery':intents['Battery'].split(':')[1]}
#
#        if inequality_simbols['time'] == '>' and time.time() - self.starting_time > values['time']:
#            current_data['Time'] = True
#        else:
#            current_data['Time'] = False # Hmm
#        if inequality_simbols['time'] == '<' and time.time() - self.starting_time < values['time']:
#            current_data['Time'] = True
#        else:
#            current_data['Time'] = False
#
#        if inequality_simbols['battery'] == '>' and self.battery[0] - self.battery[1] > values['battery']:
#            current_data['battery'] = True
#        else:
#            current_data['battery'] = False # Hmm
#        if inequality_simbols['battery'] == '<' and self.battery[0] - self.battery[1] < values['battery']:
#            current_data['battery'] = True
#        else:
#            current_data['battery'] = False
#
#        if self.min_max_height + ERROR_LIMIT_DISTANCE >=



class Mission(object):

    # Starts mission point to point. Function starts a monitor thread which constantly 
    # updates the systems location and data required for the mission.
    def execute_point_to_point(self, target, alt, quality_attributes, intents, \
        failure_flags):
        ros = ROSHandler('mavros')
        main = rospy.init_node('HoustonMonitor')
        try:
            thread.start_new_thread(ros.ros_monitor, (quality_attributes, intents, \
             failure_flags))
            ros.ros_command_takeoff(alt)
            ros.ros_command_goto(target)
            ros.ros_command_land(alt, False)

        except:
            #Error('unable to start thread').thread_error()
            raise 

    # Checks that all the required parameters for a correct mission run are present 
    def check_parameters(self, parameters):
        gen_parameters = {'Time', 'Battery', 'MaxHeight', 'MinHeight'}
        if 'QualityAttributes' in parameters:
            if not all  (param in parameters['QualityAttributes'] for param \
                in gen_parameters):
                Error("QualityAttributes description does not have enough attributes")
        else:
            Error('QualityAttributes not found.')
        if 'Intents' in parameters:
            if not all (param in parameters['Intents'] for param in gen_parameters):
                Error("Intents description does not have enough attributes")
        else:
            Error("Intents not found")
        if 'FailureFlags' in parameters:
            if not all (param in parameters['FailureFlags'] for param in gen_parameters):
                Error("FailureFlags description does not have enough attributes")
        else:
            Error("FailureFlags not found")
        return True

    # Executes mission
    def execute(self):
        mission_action = self.mission_info['Action']
        parameter_pass = self.check_parameters(self.mission_info)
        if (mission_action['Type'] == 'PTP') and parameter_pass:
            start_x = float(mission_action['x'])
            start_y = float(mission_action['y'])
            start_z = float(mission_action['z'])
            end_x   = float(mission_action['x_d'])
            end_y   = float(mission_action['y_d'])
            end_z   = float(mission_action['y_d'])
            alt     = float(mission_action['Alt'])
            quality_attributes = self.mission_info['QualityAttributes']
            intents = self.mission_info['Intents']
            failure_flags = self.mission_info['FailureFlags']
            locations = (start_x, start_y, start_z, end_x, end_y, end_z)
            self.execute_point_to_point(locations, alt, quality_attributes, intents,\
             failure_flags)
        else:
            print 'Mission type found not supported'

    def __init__(self, mission_info):
        self.robot_type  = mission_info['RobotType']
        self.launch_file = mission_info['LaunchFile']
        self.map         = mission_info['Map']
        self.mission_info = mission_info['Mission']



def check_json(json_file):
    if not 'MDescription' in json_file:
        Error('MDescription').format_error()
    elif not 'RobotType' in json_file['MDescription']:
        Error('RobotType').format_error()
    elif not 'LaunchFile' in json_file['MDescription']:
        Error('LaunchFile').format_error()
    elif not 'Map' in json_file['MDescription']:
        Error('Map').format_error()
    elif not 'Mission' in json_file['MDescription']:
        Error('Mission').format_error()
    elif not 'Name' in json_file['MDescription']['Mission']:
        Error('Mission - Name').format_error()
    elif not 'Action' in json_file['MDescription']['Mission']:
        Error('Mission - Action').format_error()
    elif not 'QualityAttributes' in json_file['MDescription']['Mission']:
        Error('Mission - QualityAttrubutes').format_error()
    elif not 'Intents' in json_file['MDescription']['Mission']:
        Error('Mission - Intents').format_error()
    elif not 'FailureFlags' in json_file['MDescription']['Mission']:
        Error('Mission - FailrueFlags').format_error()
    else:
        print Log('JSON file meets format requirements.')


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print ('Please provide a mission description file. (JSON)')
        exit()
    with open(sys.argv[1]) as file:
        json_file = json.load(file)

    check_json(json_file)
    mission = Mission(json_file['MDescription'])
    # done this way since the only mission currently supported is point to point
    mission_results = mission.execute()
    
