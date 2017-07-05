import json
import os
import sys

class ReportAnalyzer(object):

    def __init__(self, report):
        self.report_input = report
        self.report_local = {'PTP': {}, 'MPTP': {}, 'Extraction': {}}
        self.data_of_interest = {'Battery': 0, 'MaxHeight': 0, 'MinHeight': 0, 'Time': 0}
        self.total_number_specific_intents = dict(self.data_of_interest)
        self.total_number_specific_intents_violated = dict(self.data_of_interest)
        self.total_number_failure_flags = dict(self.data_of_interest)
        self.total_number_failure_flags_violated = dict(self.data_of_interest)
        self.number_of_missions = 0

    def analyze(self):
        self.populate_number_of_missions()
        self.populate_specific_intents()
        self.inform_specific_intents_by_type()
        self.populate_failure_flags()


        self.inform_number_missions_by_type()
        self.inform_specific_intents_by_type()


    def get_total_number_of_specific_intents(self):
        total_intents = 0
        for intent in self.total_number_specific_intents:
            total_intents += self.total_number_specific_intents[intent]
        return total_intents

    def inform_specific_intents_by_type(self):


        for mission_type in self.report_local:
            print '--- {} ---'.format(mission_type)
            print 'Number of Specific-Intents:   {}'.format(self.get_total_number_of_specific_intents(mission_type) )




    def populate_number_of_missions(self):
        for report in self.report_input['Reports']:
            self.number_of_missions += 1
            self.report_local[self.report_input['Reports'][report]['MissionType']][report] = \
                self.report_input['Reports'][report]

    def inform_number_missions_by_type(self):
        print 'PTP:        {}'.format(len(self.report_local['PTP']))
        print 'MPTP:       {}'.format(len(self.report_local['MPTP']))
        print 'Extraction: {}'.format(len(self.report_local['Extraction']))
        print '---------------'
        print 'Total:      {}'.format(self.number_of_missions)

    def populate_specific_intents(self):
        for mission_type in dict(self.report_local):
            specific_intents, specific_intents_violated = self.get_specific_intent_data(mission_type)
            self.report_local[mission_type]['specific_intents'] = specific_intents
            self.report_local[mission_type]['specific_intents_violated'] = specific_intents_violated
            for intent_type in specific_intents:
                self.total_number_specific_intents[intent_type] = \
                    self.total_number_specific_intents[intent_type] + specific_intents[intent_type]
                self.total_number_specific_intents_violated[intent_type] = \
                    self.total_number_specific_intents_violated[intent_type] + \
                    specific_intents_violated[intent_type]

    def populate_failure_flags(self):
        for mission_type in self.report_local:
            failure_flags, failure_flags_violated = self.get_failure_flags(mission_type)
            self.report_local[mission_type]['failure_flags'] = failure_flags
            self.report_local[mission_type]['failure_flags_violated'] = failure_flags_violated

        for interest in failure_flags:
            print interest
            self.total_number_failure_flags[interest] = \
                self.total_number_failure_flags[interest] + failure_flags[interest]
            self.total_number_failure_flags_violated[interest] = \
                self.total_number_failure_flags_violated[interest] + \
                failure_flags_violated[interest]

    def get_specific_intent_data(self, mission_type):
        total_number_specific_intents = dict(self.data_of_interest)
        total_number_specific_intents_violated = dict(self.data_of_interest)
        for mission in self.report_local[mission_type]:
            for intent in self.report_local[mission_type][mission]['Specific-Intents']:
                for specific_intent in intent:
                    total_number_specific_intents_violated[specific_intent] = \
                        total_number_specific_intents_violated[specific_intent] + 1
            for specific_intent_type in total_number_specific_intents:
                total_number_specific_intents[specific_intent_type] = \
                    total_number_specific_intents[specific_intent_type] + \
                    (len(self.report_local[mission_type][mission]['Specific-Intents']) * 4)

        return total_number_specific_intents, total_number_specific_intents_violated

    def get_failure_flags(self, mission_type):
        total_number_failure_flags = dict(self.data_of_interest)
        total_number_failure_flags_violated = dict(self.data_of_interest)

        for mission in self.report_local[mission_type]:
            if self.report_local[mission_type][mission]['Failure Flags'] != 'Success':
                cause = self.report_local[mission_type][mission]['Failure Flags'].split(' ')[0]
                if not cause in self.data_of_interest:
                    # TODO change the description of min and max height in ff
                        # to MinHeight and MaxHeight
                    if cause == 'Min':
                        total_number_failure_flags_violated['MinHeight'] = 1
                    elif cause == 'Max':
                        total_number_failure_flags_violated['MaxHeight'] = 1
                else:
                    total_number_failure_flags_violated[cause] = 1
        return total_number_failure_flags, total_number_failure_flags_violated











#        for report in self.report_local:
#            for mission in self.report_local[report]:
#                temp_mission = self.report_local[report][mission]
#                if temp_mission['Failure Flags'] != 'Success':
#                    self.report_local_stats['FailureFlags'][mission] = temp_mission['Failure Flags']
#                if not temp_mission['Genral-Intents']:
#                    self.report_local_stats['Genral-Intents'][mission] = temp_mission['Genral-Intents']
#                for index in range (0, len(temp_mission['Specific-Intents'])):
#                    if temp_mission['Specific-Intents'][index]:
#                        for concrete_specific_intent in temp_mission['Specific-Intents'][index]:
#                            print 'here'
#                            self.report_local_stats['Specific-Intents'][mission][index][concrete_specific_intent] = temp_mission['Specific-Intents'][index][concrete_specific_intent]

#        print self.report_local_stats['Specific-Intents']['1']
