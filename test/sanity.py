#!/usr/bin/env python3
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
