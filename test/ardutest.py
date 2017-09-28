#!/usr/bin/env python3
from houston.ardu.copter import ArduCopter
from houston.state import State, Environment
from houston.mission import Mission
from houston.action import Action

from pprint import pprint as pp


if __name__ == "__main__":
    system = ArduCopter('ardubugs:copter:742cdf6')

    # construct a mission
    # actions = [
    #     Action("setmode", {
    #         'mode': 'GUIDED'
    #     }),
    #     Action("arm",{'arm': True}),
    #     Action("takeoff", {
    #         'altitude': 10.0
    #     }),
    #     Action("goto", {
    #         'latitude' : -35.361354,
    #         'longitude': 149.165218,
    #         'altitude' : 15.0
    #     }),
    #     Action('setmode', {
    #         'mode': 'LAND'
    #     })
    # ]
    actions = [
        Action("setmode", {
            'mode': 'GUIDED'
        }),
        Action("arm",{'arm': True}),
        Action("arm",{'arm': True}),
        Action("arm",{'arm': False}),
        Action("arm",{'arm': True})
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
    container = system.provision()

    try:
        outcome = container.execute(mission)
        pp(outcome.to_json())
    finally:
        container.destroy()
