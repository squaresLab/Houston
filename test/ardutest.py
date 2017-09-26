#!/usr/bin/env python3
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.action import Action

from pprint import pprint as pp


if __name__ == "__main__":
    system = ArduCopter()

    # construct a mission
    actions = [
        Action("setmode", {
            'mode': 'GUIDED'
        }),
        Action("arm",{}),
        Action("takeoff", {
            'altitude': 5.0
        }),
        Action("goto", {
            'latitude' : -35.361354,
            'longitude': 149.165218,
            'altitude' : 5.0
        }),
        Action('setmode', {
            'mode': 'LAND'
        })
    ]
    environment = Environment({})
    initial = State({
        "x": 10.43,
        "y": 0.5,
        "bumper": False, # we could have defaults?
        "cliff": False,
        "orientation": 12.0,
        "battery": 30.0
    })
    mission = Mission(environment, initial, actions)

    # create a container for the mission execution
    image = 'squareslab/ardubugs:a0c5ac1'
    container = mgr.create_container(system, image)
    print("built container")

    try:
        outcome = container.execute(mission)
        pp(outcome.to_json())
    finally:
        mgr.destroy_container(container)
