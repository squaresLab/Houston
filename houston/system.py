import bugzoo
import copy
import time
import timeit
import signal
import math
import houston.state

from houston.mission import Mission, MissionOutcome
from houston.action import ActionSchema, ActionOutcome, Action
from houston.branch import BranchID, Branch, BranchPath
from houston.util import TimeoutError, printflush
from houston.state import StateVariable


class System(object):
    """
    Instances of the System class are used to provide a description of a
    system-under-test, and to provide an interface for safely interacting
    with the system-under-test in an idempotent manner.
    """
    def __init__(self,
                 snapshot: bugzoo.Bug,
                 variables: List[StateVariable],
                 schemas: List[ActionSchema]
                 ) -> None:
        self.__snapshot = snapshot
        self.__variables = {v.name: v for v in variables}
        self.__schemas = {s.name: s for s in schemas}

    @property
    def snapshot(self):
        """
        The snapshot, provided by BugZoo, used to provide access to a concrete
        implementation of this system (known as a "sandbox").
        """
        return self.__snapshot

    @property
    def branches(self):
        """
        A list of the branches for this system.
        """
        return [b for s in self.__schemas.values() for b in s.branches]

    def branch(self, iden):
        """
        Returns an outcome branch for this system provided its identifier.
        """
        assert isinstance(iden, BranchID)
        schema = self.__schemas[iden.action_name]
        return schema.branch(iden)

    def execute(self, msn, container = None):
        """
        Executes a given mission using an optionally provided container. If no
        container is provided, a fresh one will be provisioned.

        :param  msn:    the mission that should be executed.

        :return A summary of the outcome of the mission, in the form of a
                MissionOutcome
        """
        # if no container is specified, provision one.
        if container is None:
            container = self.provision()

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
                start_time = time.time()
                state_before = state_after = self.observe(0.0)

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
                        state_after = self.observe(time.time() - start_time)
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

    def observe(self, time_offset=0.0):
        """
        Returns a description of the current state of the system.

        TODO: ensure that the system is actually running!
        """
        from houston.state import State
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return State(vals, time_offset)

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
