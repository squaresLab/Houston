#!/usr/bin/env python3
#
# This script can be used to execute a given mission on a specified system,
# both of which are described by a JSON file whose path is provided as the
# sole argument to this script. The system and mission are jointly specified
# by a single JSON object, as shown below:
#
# {'system': SYSTEM, 'mission': MISSION}
#
# where SYSTEM and MISSION should be standard JSON descriptions of the system
# and mission, respectively.
#
# Example usage:
#
# ./sanity.py test-scenario-one.json
#
import sys
from houston.system import System
from houston.mission import Mission
from pprint import pprint as pp


if __name__ == "__main__":
    assert len(sys.argv, 1)
    test_file = sys.argv[1]

    # load the mission and system descriptions from file
    with open(test_file, 'r') as f:
        test = json.load(f)
    mission = Mission.from_json(test['mission'])
    system = System.from_json(test['system'])

    # execute the test and observe the outcome
    container = system.provision()
    try:
        outcome = container.execute(mission)
        pp(outcome.to_json())
    finally:
        container.destroy()
