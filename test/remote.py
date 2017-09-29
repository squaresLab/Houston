#!/usr/bin/env python3
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.container import Container
from houston.action import Action
from pprint import pprint as pp


if __name__ == "__main__":
    system = ArduCopter('ardubugs:copter:1858a05')

    # construct a mission
    actions = [
        Action("setmode", {
            'mode': 'GUIDED'
        }),
        Action("arm",{'arm': False}),
        Action("takeoff",{'altitude': 10.0})
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
    }, 0.0)   
    mission = Mission(environment, initial, actions)

    port = '8080'
    outcome = Container.send_mission_to_server(port, system, mission)
    pp(outcome.to_json())
