#!/usr/bin/env python
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.action import Action
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits

from pprint import pprint as pp

import houston.manager as mgr


image = 'squareslab/ardubugs:a0c5ac1'
system = ArduCopter()
environment = Environment({})
initial_state = State({
    "x": 10.43,
    "y": 0.5,
    "bumper": False,
    "cliff": False,
    "orientation": 12.0,
    "battery": 30.0
})

seed = 0
limits = ResourceLimits(num_missions = 1)
generator = RandomMissionGenerator(system, image, initial_state, environment)
missions = generator.generate(seed, limits)

print(missions)
