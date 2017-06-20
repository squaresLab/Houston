import random
import math
from runner import euclidean
QUALITY_ATTRUBUTE_INFORM_RATE = 5
FAILURE_FLAG_SHUTDOWN         = True

class RandomMissionGenerator(object):
    """Generates random  missions"""
    def __init__(self, name, current_model_position):
        self.name = name
        self.types = ['PTP','MPTP','Extraction']
        self.ptp_params = ['alt','x','y', 'z','x_d','y_d','z_d', ]
        self.extraction_params = list(self.ptp_params)
        self.extraction_params.append('wait')
        # Failure Flags and Quality Attributes use the same list
        self.quaility_attributes = ['ReportRate','Time','Battery','MaxHeight',\
        'MinHeight','DistanceTraveled']
        self.intents = list(self.quaility_attributes).remove('ReportRate')
        self.current_model_position = current_model_position


    def get_random_by_type(self, param):
        if param == 'alt':
            return random.randint(1, 50)
        elif param == 'wait':
            return random.randint(0,50)
        elif param in self.ptp_params:
            return random.randint(0, 50)


    def get_multiple_locations(self, number_of_locations):
        locations = []
        for x in range(number_of_locations):
            location = {}
            for param in self.ptp_params:
                if param == 'alt' or param == 'z':
                    continue
                location[param] = self.get_random_by_type(param)
            location['alt'] = self.get_random_by_type('alt')
            location['z'] = location['alt']
            locations.append(location)
        return locations


    def get_mission_action(self, psudo_random_number):
        action_data = {}

        if psudo_random_number == 0:
            action_data['Type'] = self.types[0]
            for param in self.ptp_params:
                if param == 'alt' or param == 'z':
                    continue
                action_data[param] = self.get_random_by_type(param)
            random_alt = self.get_random_by_type('alt')
            action_data['alt'] = random_alt
            action_data['z'] = random_alt
            return action_data
        elif psudo_random_number == 1:
            action_data['Type'] = self.types[1]
            action_data['Locations'] = self.get_multiple_locations(random.randint(1,10))
            return action_data
        elif psudo_random_number == 2:
            action_data['Type'] = self.types[2]
            for param in self.extraction_params:
                if param == 'alt' or param == 'z':
                    continue
                action_data[param] = self.get_random_by_type(param)
            action_data['alt'] = self.get_random_by_type('alt')
            action_data['z'] = action_data['alt']
            return action_data


    # We want all the data about the run, so we set all to true
    def get_quality_attributes(self):
        quality_attributes_data = {}
        for param in self.quaility_attributes:
            if param == 'ReportRate':
                quality_attributes_data[param] = QUALITY_ATTRUBUTE_INFORM_RATE
            quality_attributes_data[param] = True
        return quality_attributes_data

    def calculate_time_for_intents(self, mission_action, multiple_points = False):
        total_time = 0
        if multiple_points:
            total_time += float(mission_action['Locations'][0]['alt']) * 1.8
            previous_location = self.current_model_position
            for locations in mission_action['Locations']:
                total_time += euclidean((previous_location.x, previous_location.y),(\
                    locations['x'], locations['y'])) * 1.8
            total_time += float(mission_action['Locations'][0]['alt']) * 2.6
        else:
            total_time += mission_action['alt'] * 1.8
            total_time += euclidean((self.current_model_position.x, \
                self.current_model_position.y), (mission_action['x'], \
                mission_action['y'])) * 1.8
            total_time += mission_action['alt'] * 2.6


        return total_time


    def get_intents(self, mission_action):
        intents_data = {}
        if mission_action['Type'] == 'PTP':
            intents_data['Time'] = self.calculate_time_for_intents(mission_action)
        elif mission_action['Type'] == 'MPTP':
            intents_data['Time'] = self.calculate_time_for_intents(mission_action, True)
        elif mission_action['Type'] == 'Extraction':
            intents_data['Time'] = self.calculate_time_for_intents(mission_action) * 2

        if 'Locations' in  mission_action:
            intents_data['MaxHeight'] = mission_action['Locations'][0]['alt']+ 0.3
            intents_data['MinHeight'] = mission_action['Locations'][0]['alt']- 0.3
        else:
            intents_data['MaxHeight'] = mission_action['alt']+ 0.3
            intents_data['MinHeight'] = mission_action['alt']- 0.3
        intents_data['Battery']   = intents_data['Time'] * 0.0025
        return intents_data


    def get_failure_flags(self, intents):
        failure_flags_data = {}
        failure_flags_data['Time'] = intents['Time'] + 10
        failure_flags_data['Battery'] = intents['Battery'] + (0.0025 * 10) #Tecnically 10 more seconds of battery
        failure_flags_data['MaxHeight'] = intents['MaxHeight'] + 0.3
        failure_flags_data['MinHeight'] = intents['MinHeight'] - 0.3
        failure_flags_data['SystemShutdown'] = FAILURE_FLAG_SHUTDOWN
        return failure_flags_data

    def get_mission_type(self, mission_type):
        mission_types = {'PTP': 0, 'MPTP': 1, 'EXTR': 2, 'RDM': -1}
        if mission_type not in mission_types:
            print 'Mission not supported. Make sure you are selecting a valid mission.'
        return mission_types[mission_type]

    def generate_random_mission(self, mission_type):
        json = {'MDescription':{'RobotType': 'Copter','LaunchFile': 'None', 'Map':\
        'None', 'Mission': {'Name': self.name}}}
        mission_type_number = self.get_mission_type(mission_type)
        if mission_type_number == -1:
            mission_type_number = random.randint(0,len(self.types)-1)

        action  = self.get_mission_action(mission_type_number)
        quality_attributes = self.get_quality_attributes()
        intents = self.get_intents(action)
        failure_flags = self.get_failure_flags(intents)
        json['MDescription']['Mission']['Action'] = action
        json['MDescription']['Mission']['QualityAttributes'] = quality_attributes
        json['MDescription']['Mission']['Intents'] = intents
        json['MDescription']['Mission']['FailureFlags'] = failure_flags


        return json
