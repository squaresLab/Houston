import copy
import json
import state
import timeit
import signal
import math

from mission import Mission, MissionOutcome
from action import ActionSchema, ActionOutcome, Action
from branch import BranchID, Branch, BranchPath

from util import TimeoutError


class System(object):
    """
    Description of System.
    """

    def __init__(self, identifier, variables, schemas):
        """
        Constructs a new System.

        :param  identifier: a unique string identifier (i.e., a name) for this\
                            system
        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
        assert (isinstance(identifier, str) and identifier is not None)
        assert (isinstance(variables, list) and variables is not None)
        assert (isinstance(schemas, list) and schemas is not None)

        self.__identifier = identifier

        self.__variables = {v.getName(): v for v in variables}
        self.__schemas = {s.getName(): s for s in schemas}


    def toJSON(self):
        """
        Returns a JSON-based description of this system.
        """
        raise NotImplementedError


    def installed(self):
        """
        Returns true if this system is installed on this machine.
        """
        raise NotImplementedError


    def getIdentifier(self):
        """
        Returns the unique identifier (i.e., the name) for this system.
        """
        return self.__identifier


    def getBranches(self):
        """
        Returns a list of the branches for this system.
        """
        return [b for s in self.__schemas.values() for b in s.getBranches()]


    def getBranch(self, iden):
        """
        Returns an outcome branch for this sytem provided its identifier.
        """
        assert (isinstance(iden, BranchID) and iden is not None)
        schema = self.__schemas[iden.getActionName()]
        return schema.getBranch(iden)


    def setUp(self, mission):
        """
        Responsible for appropriately configuring and launching the system,
        for a given mission.
        """
        raise NotImplementedError


    def tearDown(self, mission):
        """
        Responsible for safely closing the system, following the execution of
        a given mission.
        """
        raise NotImplementedError


    def execute(self, msn):
        """
        Executes a given mission.

        :param  msn:    the mission that should be executed.

        :return A summary of the outcome of the mission, in the form of a
                MissionOutcome
        """
        assert (self.installed())
        timeBeforeSetup = timeit.default_timer()
        self.setUp(msn)
        totalSetupTime = timeit.default_timer() - timeBeforeSetup

        env = msn.getEnvironment()
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.getActions():
                schema = self.__schemas[action.getSchemaName()]

                # compute expected state
                initialState = self.getState()

                # resolve the branch and compute the expected outcome
                branch = schema.resolveBranch(action, initialState, env)
                expected = branch.computeExpectedState(action, initialState, env)

                # enforce a timeout
                timeout = schema.computeTimeout(action, initialState, env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                timeBefore = timeit.default_timer()

                try:
                    schema.dispatch(self, action, initialState, env)
                except TimeoutError:
                    pass
                finally:
                    signal.alarm(0) # does this reset the alarm?

                timeAfter = timeit.default_timer()
                timeElapsed = timeAfter - timeBefore

                print('Doing: {}'.format(action.getSchemaName()))

                # compare the observed and expected states
                observed = self.getState()
                passed = expected.isExpected(self.__variables, observed)
                outcome = ActionOutcome(action, passed, initialState, observed, timeElapsed, branch.getID())
                outcomes.append(outcome)

                if not passed:
                    totalTime = timeit.default_timer() - timeBeforeSetup
                    return MissionOutcome(False, outcomes, totalSetupTime, \
                                                                        totalTime)
            totalTime = timeit.default_timer() - timeBeforeSetup
            return MissionOutcome(True, outcomes, totalSetupTime, totalTime)

        finally:
            self.tearDown(msn)


    def getState(self):
        """
        Returns a description of the current state of the system.

        TODO: ensure that the system is actually running!
        """
        assert (self.installed())
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return state.State(vals)


    def getActionSchemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)
