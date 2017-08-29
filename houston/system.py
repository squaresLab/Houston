import copy
import json
import state
import timeit
import signal
import math
import manager as mgr

from mission import Mission, MissionOutcome
from action import ActionSchema, ActionOutcome, Action
from branch import BranchID, Branch, BranchPath

from util import TimeoutError

class System(object):
    """
    Description of System.


    Attributes:
        __variables (dict of Variable): TODO
        __schemas (dict of ActionSchema): TODO
    """


    """
    A registry of system types known to Houston, indexed by name.
    """
    _system_types = {}


    @staticmethod
    def register(name, cls):
        """
        Registers a system type under a given name.
        """
        if name in System._system_types:
            raise Error("system class already registered with name: {}".format(name))
        System._system_types[name] = cls


    @staticmethod
    def fromJSON(jsn):
        """
        Constructs a system from its JSON description.
        """
        assert (isinstance(jsn, dict))
        cls = System._system_types[jsn['type']]
        return cls.fromJSON(jsn)


    def __init__(self, variables, schemas):
        """
        Constructs a new System.

        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
        assert (isinstance(variables, list) and variables is not None)
        assert (isinstance(schemas, list) and schemas is not None)

        self.__variables = {v.getName(): v for v in variables}
        self.__schemas = {s.getName(): s for s in schemas}

    
    def typeName(self):
        """
        Returns the name used by the type of this system.
        """
        cls = type(self)
        for (n, kls) in System._system_types.items():
            if kls == cls:
                return n

        err = "attempted to determine name of unregistered system class: {}".format(cls)
        raise Exception(cls)


    def toJSON(self):
        """
        Returns a JSON-based description of this system.
        """
        return {
            'type': self.typeName()
        }


    def installed(self):
        """
        Returns true if this system is installed on this machine.
        """
        raise NotImplementedError


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
