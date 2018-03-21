#!/usr/bin/env python3
import houston
import bugzoo
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits

#bz = bugzoo.BugZoo()
#snapshot = bz.bugs['ardudemo:ardupilot:overflow']
#snapshot.build()

sut = houston.ardu.ArduRover('afrl:overflow')

# mission description
actions = [
    houston.action.Action("arm", {'arm': True}),
    houston.action.Action("goto", {
        'latitude' : -35.361354,
        'longitude': 149.165218,
        'altitude' : 5.0
    })
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
sandbox = sut.provision()
#res = sandbox.run(mission)
#print(res)
(res, coverage) = sandbox.run_with_coverage(mission, { "APMrover2/APMrover2.cpp" })
print("Done")
print(coverage.to_dict())

# mission_generator = RandomMissionGenerator(sut, initial, environment)
# resource_limits = ResourceLimits(2, 1000)
# mission_generator.generate(100, resource_limits)
#mission_generator.prepare(100, resource_limits)
#for i in range(5):
#    m = mission_generator.generate_mission()
#    print("Mission {}: {}".format(i, m.to_json()))
#    res = sandbox.run(m)
#    print(res)
