from typing import Set, Optional, Tuple, Dict
from timeit import default_timer as timer
import math
import time
import threading
import signal
import logging

import bugzoo
from bugzoo.client import Client as BugZooClient
from bugzoo.core.bug import Bug as Snapshot
from bugzoo.core.fileline import FileLineSet

from .state import State
from .mission import Mission, MissionOutcome
from .util import TimeoutError, printflush
from .action import ActionOutcome

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class Sandbox(object):
    """
    Sandboxes are used to provide an isolated, idempotent environment for
    executing test cases on a given system.
    """
    def __init__(self,
                 system: 'System',
                 client_bugzoo: BugZooClient
                 ) -> None:
        self.__lock = threading.Lock()
        self.__system = system
        self.__snapshot = system.snapshot
        self._bugzoo = client_bugzoo
        self.__container = client_bugzoo.containers.provision(self.__snapshot)
        self.__instrumented = False

    @property
    def snapshot(self) -> Snapshot:
        """
        A BugZoo snapshot of the system under test.
        """
        return self.__snapshot

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
    def bugzoo(self) -> BugZooClient:
        """
        The BugZoo daemon.
        """
        return self._bugzoo

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
        config = self.system.configuration
        self.__lock.acquire()
        try:
            time_before_setup = timer()
            logger.debug("preparing for mission")
            self._start(mission)
            setup_time = timer() - time_before_setup
            logger.debug("prepared for mission (took %.3f seconds)",
                         setup_time)

            env = mission.environment
            outcomes = []

            for action in mission:
                logger.debug('performing action: %s', action)
                schema = self.system.schemas[action.schema_name]

                # compute expected state
                start_time = time.time()
                state_before = state_after = self.observe(0.0)

                # determine which spec the system should observe
                spec = schema.resolve(action, state_before, env, config)
                logger.debug('enforcing specification: %s', spec)

                # enforce a timeout
                timeout = \
                    schema.timeout(action, state_before, env, config)
                logger.debug("enforcing timeout: %.3f seconds", timeout)
                time_before = timer()
                passed = False
                try:
                    # TODO: dispatch to this container!
                    schema.dispatch(self, action, state_before, config, env)

                    # block until the postcondition is satisfied or
                    # the timeout is hit
                    while not passed:
                        state_after = self.observe(time.time() - start_time)
                        # TODO implement idle! (add timeout in idle dispatch)
                        sat = spec.postcondition(action,
                                                 state_before,
                                                 state_after,
                                                 env,
                                                 config)
                        if sat:
                            logger.debug("command was successful")
                            passed = True
                            break
                        if timer() - time_before >= int(math.ceil(timeout)):
                            raise TimeoutError
                        time.sleep(0.1)
                        logger.debug("state: %s", state_after)

                except TimeoutError:
                    logger.debug("reached timeout before postcondition was satisfied")  # noqa: pycodestyle
                time_elapsed = timer() - time_before

                # record the outcome of the action execution
                outcome = ActionOutcome(action,
                                        passed,
                                        state_before,
                                        state_after,
                                        time_elapsed)
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

    def observe(self, running_time: float) -> None:
        """
        Returns an observation of the current state of the system running
        inside this sandbox.
        """
        variables = self.system.variables
        values = {v.name: v.read(self) for v in variables}
        values['time_offset'] = running_time
        return self.system.__class__.state.from_json(values)
