#!/usr/bin/env python3
import houston
import bugzoo
import json
from houston.generator import *
from houston.generator.resources import ResourceLimits
from houston.mission import Mission
from houston.runner import MissionRunnerPool
from houston.ardu.common.goto import CircleBasedGotoGenerator
import copy


#### Run a single mission
def run_single_mission(sandbox, mission):
    res = sandbox.run(mission)
    print(res)

#### Run a single mission with coverage
def run_single_mission_with_coverage(sandbox, mission):
    (res, coverage) = sandbox.run_with_coverage(mission)
    print("Done")
    print(coverage)

### Run all missions stored to a json file
def run_all_missions(sut, mission_file, coverage=False):
    missions = []
    with open(mission_file, "r") as f:
        missions_json = json.load(f)
        missions = list(map(Mission.from_json, missions_json))
    assert isinstance(missions, list)


    outcomes = {}
    coverages = {}
    def record_outcome(mission, outcome, coverage=None):
        outcomes[mission] = outcome
        coverages[mission] = coverage

    runner_pool = MissionRunnerPool(sut, 4, missions, record_outcome, coverage)
    print("Started running")
    runner_pool.run()
    print("Done running")
    print(outcomes)

    with open("example/failed.json", "w") as f:
        for m in outcomes:
            if not outcomes[m].passed:
                f.write(str(m.to_json()))
                f.write("\n")

    if coverage:
        from bugzoo.core.coverage import TestSuiteCoverage
        from bugzoo.core.spectra import Spectra
        from bugzoo.localization import Localization
        from bugzoo.localization.suspiciousness import tarantula
        test_suite_coverage_dict = {}
        counter = 0
        for m in coverages:
            test = {
                    'test': 't{}'.format(counter),
                    'outcome': outcomes[m].to_test_outcome_json(0),
                    'coverage': coverages[m].to_dict()
            }
            test_suite_coverage_dict['t{}'.format(counter)] = test
            counter += 1
        spectra = Spectra.from_coverage(TestSuiteCoverage.from_dict(test_suite_coverage_dict))
        l = Localization.from_spectra(spectra, tarantula)
        print(str(l.get_most_suspicious_lines()))
        with open("example/localization.json", "w") as f:
            f.write(str(l))

### Generate missions
def generate(sut, initial, environment, number_of_missions, max_num_actions=3):
    mission_generator = RandomMissionGenerator(sut, initial, environment, max_num_actions=max_num_actions, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_missions, 1000)
    missions = mission_generator.generate(100, resource_limits)
    print("### {}".format(missions))
    with open("example/missions.json", "w") as f:
        mission_descriptions = list(map(Mission.to_json, missions))
        print(str(mission_descriptions))
        json.dump(mission_descriptions, f)


### Generate and run missions
def generate_and_run(sut, initial, environment, number_of_missions):
    mission_generator = RandomMissionGenerator(sut, initial, environment)
    resource_limits = ResourceLimits(number_of_missions, 1000)
    mission_generator.generate_and_run(100, resource_limits)
    #mission_generator.prepare(100, resource_limits)
    #for i in range(number_of_missions):
    #    m = mission_generator.generate_mission()
    #    print("Mission {}: {}".format(i, m.to_json()))
    #    res = sandbox.run(m)
    print("DONE")


### Generate and run missions with mutation operator
def generate_and_run_mutation(sut, initial_state, environment, initial_mission, number_of_missions):
    mission_generator = MutationBasedMissionGenerator(sut, initial, environment, initial_mission, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_missions*5, 1000, number_of_missions)
    mission_generator.generate_and_run(100, resource_limits, with_coverage=True)
    print("DONE")
    with open("example/missions-mutation.json", "w") as f:
        mission_descriptions = list(map(Mission.to_json, mission_generator.history))
        print(str(mission_descriptions))
        json.dump(mission_descriptions, f)
        f.write("\n")
        mission_descriptions = list(map(Mission.to_json, mission_generator.most_fit_missions))
        print(str(mission_descriptions))
        json.dump(mission_descriptions, f)



### Generate and run missions with fault localization
def generate_and_run_with_fl(sut, initial, environment, number_of_missions):
    mission_generator = RandomMissionGenerator(sut, initial, environment, max_num_actions=3, action_generators=[CircleBasedGotoGenerator((-35.3632607, 149.1652351), 2.0)])
    resource_limits = ResourceLimits(number_of_missions, 1000)
    report = mission_generator.generate_and_run(100, resource_limits, with_coverage=True)
    print("DONE")
    print(report)
    print(mission_generator.coverage)
    print(mission_generator.report_fault_localization())
    with open("fl.json", "w") as f:
        f.write(str(mission_generator.report_fault_localization()))


if __name__=="__main__":
    sut = houston.ardu.ArduRover('afrl:overflow')
    #sut = houston.ardu.ArduCopter('afrl:overflow')

    # mission description
    actions = [
        houston.action.Action("arm", {'arm': True}),
        #houston.action.Action("takeoff", {'altitude': 3.0}),
        houston.action.Action("goto", {
            'latitude' : -35.361354,
            'longitude': 149.165218,
            'altitude' : 5.0
        }),
        #houston.action.Action("setmode", {'mode': 'LAND'}),
        houston.action.Action("arm", {'arm': False})
    ]
    environment = houston.state.Environment({})
    initial = houston.state.State({
        "homeLatitude" : -35.3632607,
        "homeLongitude" : 149.1652351,
        "latitude" : -35.3632607,
        "longitude": 149.1652351,
        "altitude" : 0.0,
        "battery"  : 100,
        "armed"    : False,
        "armable"  : True,
        "mode"     : "AUTO"
    }, 0.0)
    mission = houston.mission.Mission(environment, initial, actions)
    # create a container for the mission execution
    #sandbox = sut.provision()

    #run_single_mission_with_coverage(sandbox, mission)
    #generate(sut, initial, environment, 100, 10)
    #run_all_missions(sut, "example/missions.json", False)
    generate_and_run_mutation(sut, initial, environment, mission, 3)
    #generate_and_run_with_fl(sut, initial, environment, 5)
    #run_single_mission_with_coverage(sandbox, mission)

    #sandbox.destroy()
