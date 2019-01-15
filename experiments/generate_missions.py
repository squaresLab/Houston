#!/usr/bin/env python3
import copy
import json
import logging

import argparse

from houston.mission import Mission
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits

from settings import sut, initial, environment, config


def setup_logging() -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG)
    logging.getLogger('houston').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Generates missions')
    parser.add_argument('number_of_mission', type=int, action='store',
                       help='number of missions to be generated.')
    parser.add_argument('max_num_commands', type=int, action='store',
                        help='maximum number of commands in a single mission.')
    parser.add_argument('--seed', action='store', type=int,
                        default=1000,
                        help='random seed to be used by random generator.')
    parser.add_argument('--output_file', action='store', type=str,
                        default='missions.json',
                        help='the file where the results will be stored')
    args = parser.parse_args()
    return args


### Generate missions
def generate(sut, initial, environment, config, number_of_missions, max_num_commands, seed, output_file):
    mission_generator = RandomMissionGenerator(sut, initial, environment, config, max_num_commands=max_num_commands) #action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_missions, seed)
    missions = mission_generator.generate(None, resource_limits)
    with open(output_file, "w") as f:
        mission_descriptions = list(map(Mission.to_dict, missions))
        json.dump(mission_descriptions, f)


if __name__ == "__main__":
    setup_logging()
    args = setup_arg_parser()

    generate(sut, initial, environment, config, args.number_of_mission, args.max_num_commands,
             args.seed, args.output_file)
