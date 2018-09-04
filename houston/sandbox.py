from typing import Set, Optional, Tuple, Dict
from timeit import default_timer as timer
import math
import time
import threading
import signal

import bugzoo
from bugzoo.core.fileline import FileLineSet

from .state import State
from .mission import Mission, MissionOutcome
from .util import TimeoutError, printflush
from .action import ActionOutcome


class Sandbox(object):
    """
    Sandboxes are used to provide an isolated, idempotent environment for
    executing test cases on a given system.
    """
    def __init__(self, system: 'System') -> None:
        self.__lock = threading.Lock()
        self.__system = system
        self.__container = system.bugzoo.containers.provision(system.snapshot)
        self.__instrumented = False

    @property
    def system(self) -> 'System':
        """
        The system under test by this sandbox.
        """
        return self.__system

    sut = system

    @property
    def container(self) -> Optional[bugzoo.Container]:
        """
        The BugZoo container underlying this sandbox.
        """
        return self.__container

    @property
    def bugzoo(self) -> bugzoo.BugZoo:
        """
        The BugZoo daemon.
        """
        return self.system.bugzoo

    @property
    def alive(self) -> bool:
        """
        A flag indicating whether or not this sandbox is alive.
        """
        # FIXME should also check that container is alive via BugZoo API
        return self.__container is not None

    def _start(self, mission: Mission) -> None:
        """
        Starts a new SITL instance inside this sandbox for a given mission.
        """
        raise NotImplementedError

    def _stop(self) -> None:
        """
        Stops the SITL running inside this sandbox.
        """
        raise NotImplementedError

    def run_with_coverage(self,
                          mission: Mission,
                          ) -> Tuple[MissionOutcome, FileLineSet]:
        """
        Executes a given mission and returns detailed coverage information.

        Returns:
            A tuple of the form `(outcome, coverage)`, where `outcome` provides
            a concise description of the outcome of the mission execution, and
            `coverage` specifies the lines that were covered during the
            execution for each source code file belonging to the system under
            test.
        """
        bz = self.bugzoo
        # TODO: somewhat hardcoded
        if not self.__instrumented:
            self.__instrumented = True
            bz.coverage.instrument(self.container)

        # FIXME instruct BugZoo to clean coverage artifacts
        cmd = "find . -name *.gcda | xargs rm"
        bz.containers.command(self.container, cmd,
                              stdout=False, stderr=False, block=True)
        outcome = self.run(mission)
        coverage = self.bugzoo.coverage.extract(self.container)

        return (outcome, coverage)

    def run(self, mission: Mission) -> MissionOutcome:
        """
        Executes a given mission and returns a description of the outcome.
        """
        assert self.alive
        self.__lock.acquire()
        try:
            time_before_setup = timer()
            print('Setting up...')  # FIXME use logger
            self._start(mission)
            print('Setup complete.')  # FIXME use logger
            setup_time = timer() - time_before_setup

            env = mission.environment
            outcomes = []

            # execute each action in sequence
            for action in mission.actions:
                # FIXME use logger
                printflush('Performing action: {}\n'.format(action.to_json()))
                schema = self.system.schemas[action.schema_name]

                # compute expected state
                start_time = time.time()
                state_before = state_after = self.observe(0.0)

                # determine which branch the system should take
                branch = schema.resolve_branch(self.system,
                                               action,
                                               state_before,
                                               env)
                # FIXME use logger
                printflush('Taking branch: {}\n'.format(branch))

                # enforce a timeout
                timeout = \
                    schema.timeout(self.system, action, state_before, env)
                time_before = timer()
                passed = False
                try:
                    # TODO: dispatch to this container!
                    schema.dispatch(self, action, state_before, env)

                    # block until the postcondition is satisfied or
                    # the timeout is hit
                    while not passed:
                        state_after = self.observe(time.time() - start_time)
                        # TODO implement idle! (add timeout in idle dispatch)
                        sat = branch.postcondition(self.system,
                                                   action,
                                                   state_before,
                                                   state_after,
                                                   env)
                        if sat:
                            passed = True
                        if timer() - time_before >= int(math.ceil(timeout)):
                            raise TimeoutError
                        time.sleep(0.1)
                        # FIXME use logger
                        print(state_after)

                except TimeoutError:
                    pass
                time_elapsed = timer() - time_before

                # record the outcome of the action execution
                outcome = ActionOutcome(action,
                                        passed,
                                        state_before,
                                        state_after,
                                        time_elapsed,
                                        branch.id)
                outcomes.append(outcome)

                if not passed:
                    total_time = timer() - time_before_setup
                    return MissionOutcome(False,
                                          outcomes,
                                          setup_time,
                                          total_time)

            total_time = timer() - time_before_setup
            return MissionOutcome(True, outcomes, setup_time, total_time)

        finally:
            self._stop()
            self.__lock.release()

    def destroy(self) -> None:
        """
        Deallocates all resources used by this container.
        """
        if self.__container is not None:
            del self.bugzoo.containers[self.__container.id]
            self.__container = None

    delete = destroy

    def observe(self, running_time) -> None:
        """
        Returns an observation of the current state of the system running
        inside this sandbox.
        """
        assert self.alive
        vals = {n: v.read(self) for (n, v) in self.system.variables.items()}
        return State(vals, running_time)
