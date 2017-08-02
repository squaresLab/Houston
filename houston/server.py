#!/usr/bin/env python
"""
The server script should be run from within the container of the system-under-test

- implements a very simple RESTful server
"""
import time
import sys
import flask
import json

app = flask.Flask(__name__)

# the current system-under-test
SYSTEM = None


@app.route("/executeMission", methods=["POST"])
def executeMission():
    """
    Executes a specified mission.


    ## Request Parameters

        * mission: a JSON-based description of the mission that should be
            performed

    returns:    a summary of the outcome of the mission, in a JSON format
    """
    mission = json.loads(flask.request.args['mission'])
    mission = Mission.fromJSON(mission)
    outcome = SYSTEM.execute(mission)
    outcome = outcome.toJSON()
    return flask.jsonify(outcome)


def main():
    """
    The entrypoint for the `houstonserver` executable.


    Usage:

        houstonserver ardupilot 2700 &
    """
    global SYSTEM

    # fetch the system!
    # we will probably need to have some sort of registry global variable
    systemName = sys.argv[1]
    # SYSTEM = FETCH_SYSTEM(systemName)

    # we also need to accept a port number
    portNumber = int(sys.argv[2])

    # launch the server on the specified port
    app.run(port=portNumber, debug=True)


if __name__ == "__main__":
    main()
