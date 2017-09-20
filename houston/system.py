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
        assert isinstance(jsn, dict)
        cls = System._system_types[jsn['type']]
        return cls.from_json(jsn)


    def __init__(self, variables, schemas):
        """
        Constructs a new System.

        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
        assert isinstance(variables, list)
        assert isinstance(schemas, list)

        self.__variables = {v.name: v for v in variables}
        self.__schemas = {s.name: s for s in schemas}

    
    @property
    def type_name(self):
        """
        Returns the name used by the type of this system.
        """
        cls = type(self)
        for (n, kls) in System._system_types.items():
            if kls == cls:
                return n

        err = "attempted to determine name of unregistered system class: {}".format(cls)
        raise Exception(cls)


    def to_json(self):
        """
        Returns a JSON-based description of this system.
        """
        return {
            'type': self.type_name
        }


    @property
    def installed(self):
        """
        Returns true if this system is installed on this machine.
        """
        raise NotImplementedError


    @property
    def branches(self):
        """
        A list of the branches for this system.
        """
        return [b for s in self.__schemas.values() for b in s.branches]


    def branch(self, iden):
        """
        Returns an outcome branch for this sytem provided its identifier.
        """
        assert isinstance(iden, BranchID)
        schema = self.__schemas[iden.action_name]
        return schema.branch(iden)


    def setup(self, mission):
        """
        Responsible for appropriately configuring and launching the system,
        for a given mission.
        """
        raise NotImplementedError


    def tear_down(self, mission):
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
        assert self.installed
        time_before_setup = timeit.default_timer()
        self.setup(msn)
        setup_time = timeit.default_timer() - time_before_setup

        env = msn.environment
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.actions:
                schema = self.__schemas[action.schema_name]

                # compute expected state
                initial_state = self.observe()

                # resolve the branch and compute the expected outcome
                branch = schema.resolve_branch(action, initial_state, env)
                expected = branch.compute_expected_state(action, initial_state, env)

                # enforce a timeout
                timeout = schema.compute_timeout(action, initial_state, env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                time_before = timeit.default_timer()

                try:
                    schema.dispatch(self, action, initial_state, env)
                except TimeoutError:
                    pass
                finally:
                    signal.alarm(0) # does this reset the alarm?

                time_after = timeit.default_timer()
                time_elapsed = time_after - time_before

                print('Doing: {}'.format(action.schema_name))

                # compare the observed and expected states
                observed = self.observe()
                passed = expected.is_expected(self.__variables, observed)
                outcome = ActionOutcome(action,
                                        passed,
                                        initial_state,
                                        observed,
                                        time_elapsed,
                                        branch.id)
                outcomes.append(outcome)

                if not passed:
                    total_time = timeit.default_timer() - time_before_setup
                    return MissionOutcome(False,
                                          outcomes,
                                          total_setup_time,
                                          totalTime)

            total_time = timeit.default_timer() - time_before_setup
            return MissionOutcome(True, outcomes, total_setup_time, total_time)

        finally:
            self.tear_down(msn)


    def observe(self):
        """
        Returns a description of the current state of the system.

        TODO: ensure that the system is actually running!
        """
        assert self.installed
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return state.State(vals)

    
    @property
    def schemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)
