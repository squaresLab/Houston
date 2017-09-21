#!/usr/bin/env python
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.action import Action
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits
from houston.ardu.copter.goto import CircleBasedGotoGenerator

from pprint import pprint as pp

import houston.manager as mgr


image = 'squareslab/ardubugs:a0c5ac1'
system = ArduCopter()
environment = Environment({})
initial_state = State({
    "homeLatitude" : -35.3632607,
    "homeLongitude" : 149.1652351,
    "latitude" : -35.3632607,
    "longitude": 149.1652351,
    "altitude" : 0.0,
    "battery"  : 100,
    "armed"    : False,
    "armable"  : True,
    "mode"     : "AUTO"
})

action_generators = [
    CircleBasedGotoGenerator((-35.3632607, 149.1652351), 30.0)
]

seed = 0
threads = 4
limits = ResourceLimits(num_missions = 400)
generator = RandomMissionGenerator(system,
                                   image,
                                   initial_state,
                                   environment,
                                   threads=threads,
                                   action_generators=action_generators)
missions = generator.generate(seed, limits)

print(missions)
