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


# The name of the model for the robot within Gazebo
# TODO: allow command line customisation (so we can use this with other robots)
ROBOT_MODEL_NAME = "mobile_base"
COMMANDS = {"TAKEOFF": 24, "SETMODE": 176, "ARM": 400 }
HOME_COOR = (-35.3632607, 149.1652351)
ERROR_LIMIT_DISTANCE = .3 # 30cm TODO: pick a better name 


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
        self.initial_coor_set         = False
        self.starting_time            = time.time()
        self.target = target
        self.initial_lat              = 0
        self.initial_long             = 0 
        self.current_local_x          = 0
        self.current_local_y          = 0
        self.current_local_alt        = 0           #alt measures in meters (z) 
        self.current_global_lat       = 0
        self.current_global_long      = 0
        self.current_global_alt       = 0
        



    # Sets the system to GUIDED, arms and takesoff to a given altitude.
    # TODO: add mode to mission parameters? 
    def takeoff_command(self, alt):
        set_mode = rospy.ServiceProxy('/mavros/set_mode', SetMode)
        res = set_mode(0, "GUIDED")
        self.target_alt = alt

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
        while not self.current_local_alt >= alt-ERROR_LIMIT_DISTANCE:
            Log('Waiting to reach alt. Goal: '+ str(alt) +' - Current: '+ \
                str(self.current_local_alt))
            time.sleep(1)
        
    #def goto_command(self, lat, longitud):

    # Makes a service call to coomand the system to land
    def land_command(self, alt):
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        res = land(0, 0, 0, 0, alt)
        if res:
            Log("System landing...")
        else:
            Error("System is not landing.")


    # Commands the system to a given location. Verifies the end of the publications
    # by comparing the current position with the expected position.
    # Need to add z for angular displacement. 
    def goto_command(self, target):
        goto_publisher = rospy.Publisher('/mavros/setpoint_position/local',\
         PoseStamped, queue_size=10)
        pose = PoseStamped()
        pose.pose.position.x = target[0]
        pose.pose.position.y = target[1]
        pose.pose.position.z = target[2]
        initial_coor = (self.initial_lat, self.initial_long)
        current_coor = (self.current_global_lat, self.current_global_long)
        expected_lat      = None
        expected_long     = None
        expected_coor     = None
        expected_distance = None

        # 0,0 is to HOME which is the starting position of the system. 
        if target[0] == 0 and target[1] == 0:
            expected_coor = (HOME_COOR[0], HOME_COOR[1])
            expected_distance = vincenty(initial_coor, expected_coor).meters
        else:
            # Check for a better solution 
            # TODO: acount for 0 latitud  (x value)
            expected_lat = self.current_global_lat + (target[0] * 0.000008983)
            expected_long = self.current_global_long + ((target[0] * 0.000008983)/ \
                math.cos(self.current_global_lat * 0.018))

        expected_coor = (expected_lat, expected_long)
        expected_distance = vincenty(initial_coor, expected_coor).meters
        distance_traveled = vincenty(initial_coor, current_coor).meters

        local_action_time = time.time()
        Log('Expected distance to travel: ' + str(expected_distance))

        while vincenty(expected_coor, current_coor).meters >= ERROR_LIMIT_DISTANCE: 
            current_coor = (self.current_global_lat, self.current_global_long)
            distance_traveled = vincenty(initial_coor, current_coor).meters
            goto_publisher.publish(pose)
            if time.time() - local_action_time  >= 5:
                Log('Distance traveled: ' + str(distance_traveled))
                local_action_time = time.time()
                print 'Current Coor:  '+ str(current_coor)
                print 'Expected Coor: '+ str(expected_coor)

        Log('Position reached')

    # Callback for local position sub
    def ros_monitor_callback_local_position(self, data):
        self.current_local_lat = data.pose.pose.position.x
        self.current_local_long = data.pose.pose.position.y
        self.current_local_alt = data.pose.pose.position.z

    # Callback for global position sub
    def ros_monitor_callback_global_position(self, data):
        if not self.initial_coor_set:
            self.initial_lat     = data.latitude
            self.initial_long    = data.longitude
            self.initial_coor_set= True
        self.current_global_lat  = data.latitude
        self.current_global_long = data.longitude
        self.current_global_alt  = data.altitude



    # Starts two subscribers to populate the system's location. It also ensures 
    # failure flags. *More to be added 
    def ros_monitor(self, quality_attributes, intents, failure_flags):        
        local_pos = rospy.Subscriber('/mavros/global_position/local', Odometry \
         , self.ros_monitor_callback_local_position)
        global_pos = rospy.Subscriber('/mavros/global_position/global', NavSatFix \
         , self.ros_monitor_callback_global_position)
        
        temp_time = time.time()
        while not rospy.is_shutdown():
            current_time = time.time()

            if  (current_time - temp_time) > 10.0:
                Log('Current time: ' + str(time.time() - self.starting_time))
                temp_time = current_time

            if  (current_time - self.starting_time) > float(failure_flags['Time']):
                Log('Mission Failed')
                rospy.signal_shutdown('Life')
                exit()

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
            ros.takeoff_command(alt)
            ros.goto_command(target)
            ros.land_command(alt)

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
    
