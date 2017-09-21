#!/usr/bin/env python
#
# You'll notice a rather large number of threads are being used by the test
# generation process. Running the system under test and the simulator is
# exceptionally cheap -- most of the time seems to be spent idling. After
# tinkering around, we found that throughput was maximised when the
# threads-to-cores ratio was set to around 8:1.
#
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
threads = 16
limits = ResourceLimits(num_missions = 500)
generator = RandomMissionGenerator(system,
                                   image,
                                   initial_state,
                                   environment,
                                   threads=threads,
                                   action_generators=action_generators)
report = generator.generate(seed, limits)

pp(report.to_json())
