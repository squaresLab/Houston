#!/usr/bin/python2.7

# TODO: Description!

import time
import json
import os
import sys
import thread
import math

import rospy
import xmlrpclib

from geopy.distance    import great_circle
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


class Error(object):

    def __init__(self, error):
        print '[ERROR]: ' + error

class Log(object):

    def __init__(self, log):
        print '[LOG]: ' + log


class ROSHandler(object):
    def __init__ (self, target):
        self.mission_info               = None
        self.mission_on                 = True
        self.initial_set                = [False, False, False, False]
        self.starting_time              = time.time()
        self.target                     = target
        self.battery                    = [0,0]
        self.min_max_height             = [-1,0]
        self.lock_min_height            = True
        self.initial_global_coordinates = [0,0]
        self.initial_local_position     = [0,0,0]
        self.initial_odom_position      = [0,0,0]
        self.current_global_coordinates = [0,0]
        self.current_local_position     = [0,0,0]
        self.current_odom_position      = [0,0,0]
        self.global_alt                 = [0,0]
        

    def check_mavros(self):
        m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
        code, status_message, uri = m.lookupNode('/mavros', '/mavros')
        if code == 1:
            return True
        else:
            return False


    def check_goto_completion(self, expected_coor, pose, pub):
        local_action_time = time.time()
        success = True
        r = rospy.Rate(10)

        remaining_distance = euclidean((pose.pose.position.x,pose.pose.position.y), \
            (self.current_odom_position[0], self.current_odom_position[1]))
        while remaining_distance >0:
            r.sleep()
            pub.publish(pose)
            local_action_time = self.inform_time(local_action_time, 2,\
                'Remaining: ' + str(remaining_distance))

        if great_circle(self.current_global_coordinates,expected_coor).meters\
            >= ERROR_LIMIT_DISTANCE:
            success = False
        time.sleep(STABLE_BUFFER_TIME)
        return success

    def check_land_completion(self, alt, wait = STABLE_BUFFER_TIME):
        local_action_time = time.time()
        success = True
        self.lock_min_height = True
        while self.current_local_position[2] >= ERROR_LIMIT_DISTANCE and \
            self.mission_on:
            local_action_time = self.inform_time(local_action_time, 5, \
            'Waiting to reach land. Goal: ~0' +' - Current: '\
                +str(self.current_local_position[2]))
        if self.current_local_position[2] >= ERROR_LIMIT_DISTANCE:
            success = False
        time.sleep(wait)
        return success



    def check_takeoff_completion(self, alt):
        local_action_time = time.time()
        success = True
        
        while ((alt+(ERROR_LIMIT_DISTANCE/2)) >= self.current_local_position[2]) \
            and (self.current_local_position[2] <= (alt-(ERROR_LIMIT_DISTANCE/2)))\
            and self.mission_on:
                local_action_time = self.inform_time(local_action_time, 5, \
                'Waiting to reach alt. Goal: '+ str(alt) +' - Current: '\
                +str(self.current_local_position[2]))
        self.lock_min_height = False
        if self.min_max_height[0] == -1:
            self.min_max_height[0] = self.current_local_position[2]
        if ((alt+(ERROR_LIMIT_DISTANCE/2)) >= self.current_local_position[2]) \
            and (self.current_local_position[2] <= (alt-(ERROR_LIMIT_DISTANCE/2))):
            success = False
        time.sleep(STABLE_BUFFER_TIME)
        return success

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
        succes = self.check_takeoff_completion(alt)
        if succes:
            Log('System reached height')
        else:
            Log('System did not reach height on time')
        
        
    #def goto_command(self, lat, longitud):

    # Makes a service call to coomand the system to land
    def ros_command_land(self, alt, wait = None):
        land = rospy.ServiceProxy('/mavros/cmd/land', CommandTOL)
        res = land(0, 0, 0, 0, alt)
        if res:
            Log("System landing...")
        else:
            Error("System is not landing.")
        if wait == None:
            success = self.check_land_completion(alt)
        else:
            success = self.check_land_completion(alt, wait)
        if success:
            Log('System has landed')
        else:
            Log('System did not land on time ')


    # Gets the current x and y values using latitude and longitud instead of 
    # getting the values form odom 
    def get_current_x_y(self):
        x = great_circle(HOME_COORDINATES, ( HOME_COORDINATES[0], \
            self.current_global_coordinates[1],)).meters
        y = great_circle(HOME_COORDINATES, (self.current_global_coordinates[0],\
         HOME_COORDINATES[1],)).meters
        if HOME_COORDINATES[0]> self.current_global_coordinates[0]:
            y *= -1
        if HOME_COORDINATES[1]> self.current_global_coordinates[1]:
            x *= -1


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
            
            expected_distance = great_circle(self.initial_global_coordinates, \
                expected_coor).meters
            Log('Using home coordinates: initial' + str(self.initial_global_coordinates)\
                + ' expected: ' + str(expected_coor))
        else:
            current_x, current_y = self.get_current_x_y()
            x_y = (current_x, current_y)
            x_distance = euclidean((target['x'], 0),(current_y, 0)) - \
                ERROR_LIMIT_DISTANCE
            y_distance = euclidean((0, target['y']),(0, current_y)) - \
                ERROR_LIMIT_DISTANCE
            expected_lat, expected_long = self.get_expected_lat_long(x_y, target, \
                x_distance, y_distance)
            expected_coor = (expected_lat, expected_long)
            Log('Using other coordinates: initial' + str(\
                self.initial_global_coordinates)\
                + ' expected: ' + str(expected_coor))
            expected_distance = great_circle(self.initial_global_coordinates, \
                expected_coor).meters


        self.current_global_coordinates = self.initial_global_coordinates
        Log('Remaining distance to travel :  ' + str( great_circle(\
            self.current_global_coordinates,expected_coor).meters))
        success = self.check_goto_completion(expected_coor, pose, goto_publisher)
        if success:
            Log('Position reached')
        else:
            Log('System did not reach position on time')

    # Callback for local position sub. It also updates the min and the max height
    def ros_monitor_callback_local_position(self, data):
        if data.pose.position.z > self.min_max_height[1]:
            self.min_max_height[1] = data.pose.position.z
        if data.pose.position.z < self.min_max_height[0] and not \
            self.lock_min_height:
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

    def ros_monitor_callback_odom_local_position(self, data):
        if not self.initial_set[3]:
            self.initial_odom_position[0]         = data.pose.pose.position.x 
            self.initial_odom_position[1]         = data.pose.pose.position.y
            self.initial_odom_position[2]         = data.pose.pose.position.z
            self.initial_set[3]                   = True
        self.current_odom_position[0]             = data.pose.pose.position.x
        self.current_odom_position[1]             = data.pose.pose.position.y
        self.current_odom_position[3]             = data.pose.pose.position.z



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
        if time.time() - self.starting_time >= float(failure_flags['Time']):
            return True, 'Time exceeded'
        elif self.battery[0] - self.battery[1] >= float(failure_flags['Battery']):
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
            'MaxHeight': self.current_local_position[2]}
        if self.min_max_height[1]<= intents['MinHeight']:
            current_data['MinHeight'] = {'Time':current_time, 'Success':False, \
            'MinHeight': self.current_local_position[2]}
        return current_data


    # Starts two subscribers to populate the system's location. It also ensures 
    # failure flags. *More to be added 
    def ros_monitor(self, quality_attributes, intents, failure_flags):        
        local_pos_sub   = rospy.Subscriber('/mavros/local_position/pose', \
            PoseStamped \
         , self.ros_monitor_callback_local_position, queue_size=10)
        global_pos_sub  = rospy.Subscriber('/mavros/global_position/global', \
            NavSatFix \
         , self.ros_monitor_callback_global_position)
        battery_sub     = rospy.Subscriber('/mavros/battery', BatteryStatus, \
          self.ros_monitor_callback_battery)
        local_odom_sub  = rospy.Subscriber('/mavros/local_position/odom', \
            Odometry, self.ros_monitor_callback_odom_local_position)


        intents_for_report = {'Time': True, 'Battery': True, 'MaxHeight':True,\
        'MinHeight': True}
        report_data = {'QualityAttributes':[],'Intents':intents_for_report,\
        'FailureFlags':'None'}
        temp_time   = time.time() #time used for failure flags and time inform
        qua_time    = time.time() #time used for the rate of attribute reports
        while self.mission_on:
            temp_time = self.inform_time(temp_time)
            fail, reason = self.check_failure_flags(failure_flags)
            if fail:
                report_data['FailureFlags'] = reason
                self.mission_on = False
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
            Error('Missing mavros')
            sys.exit()
        return ros, main

    # Starts mission point to point. Function starts a monitor thread which constantly 
    # updates the systems location and data required for the mission.
    def execute_point_to_point(self, action_data, quality_attributes, intents, \
        failure_flags, mission_info):
        ros, main = self.initial_check()
        try:
            ros.ros_set_mission_info(mission_info)
            thread.start_new_thread(ros.ros_monitor, (quality_attributes, intents, \
             failure_flags))
            time.sleep(2) # TODO Check for populated
            ros.ros_command_takeoff(action_data['alt']) #position 6 is alt
            ros.ros_command_goto(action_data, False)
            ros.ros_command_land(action_data['alt'])
            ros.ros_set_mission_over()

        except:
            #Error('unable to start thread').thread_error()
            raise 

    def execute_multiple_point_to_point(self, action_data, quality_attributes,\
        intents, failure_flags, mission_info):
        ros, main = self.initial_check()
        try:
            ros.ros_set_mission_info(mission_info)
            thread.start_new_thread(ros.ros_monitor, (quality_attributes, intents, \
                failure_flags))
            time.sleep(2)
            # TODO: Mulitple altitudes 
            ros.ros_command_takeoff(action_data[0]['alt'])
            for target in action_data:
                ros.ros_command_goto(target, True)
            ros.ros_command_land(action_data[0]['alt'])
            ros.ros_set_mission_over()
        except:
            raise

    def execute_extraction(self, action_data, quality_attributes, intents, \
        failure_flags, mission_info):
        ros, main = self.initial_check()
        
        try:
            ros.ros_set_mission_info(mission_info)
            thread.start_new_thread(ros.ros_monitor, (quality_attributes, intents, \
                failure_flags))
            time.sleep(2)
            initial_x_y = ros.get_current_x_y()
            ros.ros_command_takeoff(action_data['alt'])
            ros.ros_command_goto(action_data, False)
            ros.ros_command_land(action_data['alt'], action_data['wait']) # 7 wait time
            ros.ros_command_takeoff(action_data['alt'])
            action_data['x'] = initial_x_y[0]
            action_data['y'] = initial_x_y[1]
            ros.ros_command_goto(action_data, False)
            ros.ros_command_land(action_data['alt'])
            ros.ros_set_mission_over()
        except:
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
            if not all (param in parameters['FailureFlags'] \
                for param in gen_parameters):
                Error("FailureFlags description does not have enough attributes")
        else:
            Error("FailureFlags not found")
        return True

    def get_params(self, mission_action, multiple_actions = False):
        params_to_return = {'x':None,'y':None,'z':None,'x_d':None,'y_d':None,\
        'z_d':None,'alt':None,'wait':None,'Type':None}
        params_to_return_multiple_case = []
        if multiple_actions:
            count = 0
            for locations in mission_action['Locations']:
                params = {'x':None,'y':None,'z':None,'x_d':None,'y_d':None,\
                'z_d':None,'alt':None,'wait':None,'Type':None}
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
        mission_action = self.mission_info['Action']
        parameter_pass = self.check_parameters(self.mission_info)
        quality_attributes = self.mission_info['QualityAttributes']
        intents = self.mission_info['Intents']
        failure_flags = self.mission_info['FailureFlags']

        if (mission_action['Type'] == 'PTP') and parameter_pass:
            action_data = self.get_params(mission_action)
            self.execute_point_to_point(action_data, quality_attributes, intents,\
             failure_flags, self)
        elif (mission_action['Type'] == 'MPTP' and parameter_pass):
            action_data = self.get_params(mission_action, True)
            self.execute_multiple_point_to_point(action_data,quality_attributes,\
                intents,failure_flags, self)
        elif (mission_action['Type'] == 'Extraction' and parameter_pass):
            action_data = self.get_params(mission_action)
            self.execute_extraction(action_data,quality_attributes,\
                intents,failure_flags, self)
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


def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert len(a) != []
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)



if __name__ == "__main__":
    if len(sys.argv) < 2:
        print ('Please provide a mission description file. (JSON)')
        exit()
    with open(sys.argv[1]) as file:
        json_file = json.load(file)

    check_json(json_file)
    mission = Mission(json_file['MDescription'])
    mission_results = mission.execute()
