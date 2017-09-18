#!/usr/bin/env python
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.action import Action

import houston.manager as mgr


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
        Action('land', {})
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
    image = 'houston-icse-2018:base'
    container = mgr.createContainer(system, image)

    try:
        outcome = container.execute(mission)
        print(outcome)
    finally:
        mgr.destroyContainer(container)
