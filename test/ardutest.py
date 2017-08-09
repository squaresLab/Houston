from system import *
from ardupilot import *
from state import *
from mission import *
import houston
if __name__ == "__main__":
    system = houston.getSystem('ardupilot')
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


    missionOutcome = system.execute(Mission(environment, initial, actions)).toJSON()
    print missionOutcome
