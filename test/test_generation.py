import pytest
import attr

from houston.ardu.configuration import Configuration as ArduConfig
from houston.ardu.copter.state import State as CopterState
from houston.ardu.copter.copter import ArduCopter
from houston.environment import Environment
from houston.generator.rand import RandomMissionGenerator
from houston.generator.resources import ResourceLimits

def test_random():
    config = ArduConfig(
        speedup=1,
        time_per_metre_travelled=5.0,
        constant_timeout_offset=1.0,
        min_parachute_alt=10.0)
    environment = Environment({})
    initial = CopterState(
        home_latitude=-35.3632607,
        home_longitude=149.1652351,
        latitude=-35.3632607,
        longitude=149.1652351,
        altitude=0.0,
        armed=False,
        armable=True,
        mode="GUIDED",
        ekf_ok=True,
        yaw=0.0,
        roll=0.0,
        pitch=0.0,
        roll_channel=0.0,
        throttle_channel=0.0,
        heading=0.0,
        groundspeed=0.0,
        airspeed=0.0,
        vx=0.0,
        vy=0.0,
        vz=0.0,
        time_offset=0.0)
    sut = ArduCopter
    max_num_commands = 5
    number_of_missions = 10

    mission_generator = RandomMissionGenerator(sut, initial, environment, config, max_num_commands=max_num_commands)
    resource_limits = ResourceLimits(number_of_missions, 1000)
    missions = mission_generator.generate(100, resource_limits)

    assert len(missions) == number_of_missions
    assert all(len(m.commands) <= max_num_commands for m in missions)
