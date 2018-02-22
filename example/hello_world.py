#!/usr/bin/env python3
import houston
import bugzoo

bz = bugzoo.BugZoo()
snapshot = bz.bugs['ardudemo:ardupilot:overflow']
snapshot.build()

sut = houston.ardu.ArduRover(snapshot)

# mission description
actions = [
    houston.action.Action("arm", {}),
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
m = sandbox.run(mission)
print(m)

# execute the mission

