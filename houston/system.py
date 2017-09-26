import copy
import json
import state
import time
import timeit
import signal
import math

from mission import Mission, MissionOutcome
from action import ActionSchema, ActionOutcome, Action
from branch import BranchID, Branch, BranchPath

from util import TimeoutError, printflush


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
    def from_json(jsn):
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


    def provision(self):
        """
        Provisions a container for this system.
        """
        from system import SystemContainer
        artefact = self.repairbox_artefact
        return SystemContainer.provision(self, artefact)


    @property
    def repairbox_artefact(self):
        """
        Returns the RepairBox artefact used by this system.
        """
        raise NotImplementedError


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
        print('Setting up...'),
        self.setup(msn)
        print('Setup complete.')
        setup_time = timeit.default_timer() - time_before_setup

        env = msn.environment
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.actions:
                printflush('Performing action: {}\n'.format(action.to_json()))
                schema = self.__schemas[action.schema_name]

                # compute expected state
                state_before = state_after = self.observe()

                # determine which branch the system should take
                branch = schema.resolve_branch(self, action, state_before, env)
                printflush('Taking branch: {}\n'.format(branch))

                # enforce a timeout
                timeout = schema.timeout(self, action, state_before, env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                time_before = timeit.default_timer()
                passed = False
                try:
                    schema.dispatch(self, action, state_before, env)

                    # block until the postcondition is satisfied (or timeout is hit)
                    while not passed:
                        state_after = self.observe()
                        # TODO implement idle! (add timeout in idle dispatch)
                        if branch.postcondition(self, action, state_before, state_after, env):
                            passed = True
                        time.sleep(0.1)
                        print(state_after)

                except TimeoutError:
                    pass
                finally:
                    signal.alarm(0) # does this reset the alarm?

                time_after = timeit.default_timer()
                time_elapsed = time_after - time_before

                # record the outcome of the action execution
                outcome = ActionOutcome(action,
                                        passed,
                                        state_before,
                                        state_after,
                                        time_elapsed,
                                        branch.id)
                outcomes.append(outcome)

                if not passed:
                    total_time = timeit.default_timer() - time_before_setup
                    return MissionOutcome(False,
                                          outcomes,
                                          setup_time,
                                          total_time)

            total_time = timeit.default_timer() - time_before_setup
            return MissionOutcome(True, outcomes, setup_time, total_time)

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

    
    def variable(self, v):
        return self.__variables[v]


    @property
    def variables(self):
        return copy.copy(self.__variables)


    @property
    def schemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.copy(self.__schemas)
