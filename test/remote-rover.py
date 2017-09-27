#!/usr/bin/env python3
from houston.ardu.rover import ArduRover
from houston.state import State, Environment
from houston.mission import Mission
from houston.container import Container
from houston.action import Action
from pprint import pprint as pp


if __name__ == "__main__":
    system = ArduRover()

    # construct a mission
    actions = [
        Action("arm", {}),
        Action("goto", {
            'latitude' : -35.361354,
            'longitude': 149.165218,
            'altitude' : 5.0
        })
    ]
    environment = Environment({})
    initial = State({
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
    mission = Mission(environment, initial, actions)

    port = '8080'
    outcome = Container.send_mission_to_server(port, system, mission)
    pp(outcome.to_json())
