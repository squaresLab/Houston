"""
The server script should be run from within the container of the system-under-test

- implements a very simple RESTful server
"""
import time
import sys

# the current system-under-test
SYSTEM = None

# We need to interact with a registered (named) system

@app.route("/executeMission")
def executeMission(mission):
    """


    param:  mission:    a JSON-based description of the mission that should be
                        performed

    returns:    a summary of the outcome of the mission, in a JSON format
    """


    pass


def main():
    """
    The entrypoint for the `houstonserver` executable.


    Usage:
        
        houstonserver ardupilot &
    """
    global SYSTEM

    # fetch the system!
    # we will probably need to have some sort of registry global variable
    systemName = sys.argv[1]
    SYSTEM = DO_SOMETHING(systemName)

    # launch the server
    pass

    # spin!
    while True:
        time.sleep(0.5)


if __name__ == "__main__":
    main()
