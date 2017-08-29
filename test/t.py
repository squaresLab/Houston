#!/usr/bin/env python
import houston
import houston.manager as mgr
from houston.mission import Mission
from houston.ardu import ArduCopter

image = "houston-icse-2018:base"
system = ArduCopter()

mission = {
    "environment": {
      "constants": {
        "map": "world"
      }
    },
    "actions": [
      {
        "kind": "goto",
        "parameters": {
          "latitude": -35.363299558959476,
          "altitude": 10,
          "longitude": 149.16531104845637
        }
      },
      {
        "kind": "arm",
        "parameters": {}
      },
      {
        "kind": "setmode",
        "parameters": {
          "mode": "GUIDED"
        }
      },
      {
        "kind": "takeoff",
        "parameters": {
          "altitude": 87.96803838155091
        }
      },
      {
        "kind": "takeoff",
        "parameters": {
          "altitude": 61.04809354203854
        }
      },
      {
        "kind": "arm",
        "parameters": {}
      },
      {
        "kind": "arm",
        "parameters": {}
      },
      {
        "kind": "goto",
        "parameters": {
          "latitude": -35.363042524654034,
          "altitude": 10,
          "longitude": 149.16526961618274
        }
      },
      {
        "kind": "goto",
        "parameters": {
          "latitude": -35.36322010731532,
          "altitude": 10,
          "longitude": 149.1652257505367
        }
      },
      {
        "kind": "arm",
        "parameters": {}
      }
    ],
    "initialState": {
      "variables": {
        "battery": 100,
        "altitude": 0,
        "longitude": 149.1652351,
        "homeLongitude": 149.1652351,
        "homeLatitude": -35.3632607,
        "mode": "AUTO",
        "latitude": -35.3632607,
        "armed": False,
        "armable": True
      }
    }
}
mission = Mission.fromJSON(mission)


try:
    cntr = None
    cntr = mgr.createContainer(system, image, verbose=True)
    outcome = cntr.execute(mission)
    print(outcome)
finally:
    if cntr:
        mgr.destroyContainer(cntr)
