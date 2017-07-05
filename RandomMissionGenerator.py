import random
import math
from houston import euclidean
QUALITY_ATTRUBUTE_INFORM_RATE = 5
FAILURE_FLAG_SHUTDOWN         = True

class RandomMissionGenerator(object):
    """Generates random  missions"""
    def __init__(self, name, current_model_position):
        self.name = name
        self.types = ['PTP','MPTP','Extraction']
        self.ptp_params = ['alt','x','y', 'z','x_d','y_d','z_d']
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
            return random.randint(1,50)
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

    def calculate_time_for_general_intents(self, mission_action, multiple_points = False):
        total_time = 0
        if multiple_points:
            total_time += self.calculate_time_takeoff(float(mission_action['Locations'][0]['alt']))
            previous_location = self.current_model_position
            for locations in mission_action['Locations']:
                total_time += self.calculate_time_from_point_to_point((previous_location.x, previous_location.y),(locations['x'], locations['y']))
            total_time += self.calculate_time_land(float(mission_action['Locations'][0]['alt']))
        else:
            total_time += self.calculate_time_takeoff(mission_action['alt'])
            total_time += self.calculate_time_from_point_to_point((self.current_model_position.x,\
                self.current_model_position.y), (mission_action['x'], mission_action['y']))
            total_time += self.calculate_time_land(mission_action['alt'])
        return total_time

    def calculate_time_from_point_to_point(self, _from, _to):
        return euclidean(_from, _to) * 1.8 # TODO

    def calculate_time_land(self, alt):
        return alt * 2.6 # TODO

    def calculate_time_takeoff(self, alt):
        return alt * 1.8 # TODO

    def get_specific_intents(self, locations):
        specific_intents = [{}]
        lowest_highest = [0,0]

        for index in range(0, len(locations)):
            if index == 0:
                specific_intents[0]['Time'] = self.calculate_time_from_point_to_point((\
                    self.current_model_position.x, self.current_model_position.y), \
                    (locations[0]['x'], locations[0]['y']))
                specific_intents[0]['Battery'] = specific_intents[0]['Time'] * 0.0025
                specific_intents[0]['MaxHeight'] = locations[0]['alt'] + 0.3
                specific_intents[0]['MinHeight'] = locations[0]['alt'] - 0.3
                lowest_highest[0] =  locations[0]['alt'] - 0.3
                lowest_highest[1] =  locations[0]['alt'] + 0.3
            else:
                specific_intents.append({})
                specific_intents[index]['Time'] = self.calculate_time_from_point_to_point((\
                    locations[index-1]['x'], locations[index-1]['y']), (locations[index]['x'], \
                    locations[index]['y']))
                specific_intents[index]['Battery'] = specific_intents[index]['Time'] * 0.0025
                if   float(locations[index]['alt']) > float(locations[index - 1]['alt']):
                    if float(locations[index]['alt']) > lowest_highest[1]:
                        lowest_highest[1] = float(locations[index]['alt'] +0.3)
                    specific_intents[index]['MaxHeight'] = float(locations[index]['alt'] + 0.3)
                    specific_intents[index]['MinHeight'] = float(locations[index - 1]['alt'] - 0.3)
                elif float(locations[index]['alt']) < float(locations[index - 1]['alt']):
                    if float(locations[index]['alt']) < lowest_highest[0]:
                        lowest_highest[0] = float(locations[index]['alt'])
                    specific_intents[index]['MaxHeight'] = float(locations[index - 1]['alt'] + 0.3)
                    specific_intents[index]['MinHeight'] = float(locations[index]['alt'] - 0.3)
                else:
                    specific_intents[index]['MaxHeight'] = float(locations[index]['alt'] + 0.3)
                    specific_intents[index]['MinHeight'] = float(locations[index]['alt'] - 0.3)

        return specific_intents, lowest_highest

    def process_PTP_intents(self, intents_data, mission_action):
        intents_data['General']['Time'] = self.calculate_time_for_general_intents(mission_action)
        intents_data['General']['MaxHeight'] = mission_action['alt']+ 0.3
        intents_data['General']['MinHeight'] = mission_action['alt']- 0.3
        intents_data['General']['Battery']   = intents_data['General']['Time'] * 0.0025
        specific_intents, lowest_highest = self.get_specific_intents(list([mission_action]))
        intents_data['Specific'] = specific_intents
        return intents_data

    def process_MPTP_intents(self, intents_data, mission_action):
        # We get first the specific intents to check which position is going to be
        # the lowest and the highest.
        specific_intents, lowest_highest = self.get_specific_intents(mission_action['Locations'])
        intents_data['General']['Time'] = self.calculate_time_for_general_intents(mission_action, True)
        intents_data['General']['MaxHeight'] = lowest_highest[1]
        intents_data['General']['MinHeight'] = lowest_highest[0]
        intents_data['General']['Battery']   = intents_data['General']['Time'] * 0.0025
        intents_data['Specific'] = specific_intents
        return intents_data

    def process_Extraction_intents(self, intents_data, mission_action):
        intents_data =  self.process_PTP_intents(intents_data, mission_action)
        intents_data['General']['Time'] = intents_data['General']['Time'] * 2
        intents_data['General']['Battery'] = intents_data['General']['Battery'] * 2
        previous_mission_action = dict(mission_action)
        previous_mission_action['x'] = self.current_model_position.x
        previous_mission_action['y'] = self.current_model_position.y
        locations = [mission_action, previous_mission_action]

        specific_intents, lowest_highest = self.get_specific_intents(locations)
        intents_data['Specific'] = specific_intents
        return intents_data

    def get_intents(self, mission_action):
        intents_data = {'General': {}, 'Specific': {}}
        if mission_action['Type'] == 'PTP':
            intents_data = self.process_PTP_intents(intents_data, mission_action)
        elif mission_action['Type'] == 'MPTP':
            intents_data = self.process_MPTP_intents(intents_data, mission_action)
        elif mission_action['Type'] == 'Extraction': # Extraction
            intents_data = self.process_Extraction_intents(intents_data, mission_action)

        return intents_data


    def get_failure_flags(self, intents):
        failure_flags_data = {}
        failure_flags_data['Time'] = intents['General']['Time'] + 10
        failure_flags_data['Battery'] = intents['General']['Battery'] + (0.0025 * 10) #Tecnically 10 more seconds of battery
        failure_flags_data['MaxHeight'] = intents['General']['MaxHeight'] + 1.5
        failure_flags_data['MinHeight'] = intents['General']['MinHeight'] - 1.5
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
