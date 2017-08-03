"""
This server script is run inside system containers. The server implements a
single endpoint that accepts the name of a system (i.e., its identifier), and
a description of a mission that should be executed; the server proceeds to
execute this mission, and returns a summary of its outcome in a JSON format.
"""
import sys
import flask
import json
import houston


app = flask.Flask(__name__)


@app.route("/executeMission", methods=["POST"])
def executeMission():
    """
    Executes a specified mission.


    ## Request Parameters

        * system:   the identifier of the system-under-test
        * mission:  a JSON-based description of the mission that should be\
            performed

    returns:    a summary of the outcome of the mission, in a JSON format
    """
    assert('system' in flask.request.args)
    assert('mission' in flask.request.args)

    # TODO: need to ensure that the system is actually imported
    system = flask.request.args['system']
    system = houston.getSystem(system)

    mission = json.loads(flask.request.args['mission'])
    mission = houston.mission.Mission.fromJSON(mission)

    outcome = system.execute(mission)
    outcome = outcome.toJSON()
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

    portNumber = int(sys.argv[1])
    app.run(port=portNumber, debug=True)


if __name__ == "__main__":
    main()
