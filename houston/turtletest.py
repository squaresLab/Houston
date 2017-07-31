from turtlebot import *
from system    import *

if __name__ == "__main__":
    system = TurtleBot()
    actions = [
        Action("goto", {
            'x': 0.0,
            'y': 5.0
        })
    ]
    environment = Environment({
        'launch_file': 'robotest.launch',
        'launch_parameters': {
        }
    })
    initialInternalState = InternalState({
        "x": 10.43,
        "y": 0.5,
        "bumper": False, # we could have defaults?
        "cliff": False,
        "orientation": 12.0,
        "battery": 30.0
    })
    initialExternalState = ExternalState({
    })

    system.execute(Mission(environment, initialInternalState, initialExternalState, actions))
