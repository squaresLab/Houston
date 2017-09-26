"""
This server script is run inside system containers. The server implements a
single endpoint that accepts the name of a system (i.e., its identifier), and
a description of a mission that should be executed; the server proceeds to
execute this mission, and returns a summary of its outcome in a JSON format.
"""
import sys
import flask
import json

from houston.system import System
from houston.mission import Mission

import houston.ardu


app = flask.Flask(__name__)


@app.route("/executeMission", methods=["POST"])
def execute_mission():
    """
    Executes a specified mission.


    ## Request Parameters

        * system:   the identifier of the system-under-test
        * mission:  a JSON-based description of the mission that should be\
            performed

    returns:    a summary of the outcome of the mission, in a JSON format
    """
    assert('system' in flask.request.json)
    assert('mission' in flask.request.json)

    systm = flask.request.json['system']
    msn = flask.request.json['mission']

    systm = System.from_json(systm)
    msn = Mission.from_json(msn)

    outcome = systm.execute(msn)
    outcome = outcome.to_json()
    return flask.jsonify(outcome)


def main():
    """
    The entrypoint for the `houstonserver` executable.

    Command-Line Parameters:

        * port: the number of the port that the server should run on.

    Usage:

        houstonserver 2700 &
    """
    if len(sys.argv) != 2:
        print("ERROR: unspecified port number")
        exit(1)

    port_number = int(sys.argv[1])
    app.run(host='0.0.0.0', port=port_number, use_reloader=False) #debug=True)

if __name__ == "__main__":
    main()
