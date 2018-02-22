import math
import bugzoo
import signal
import time
import threading
from timeit import default_timer as timer
from typing import Optional
from houston.state import State
from houston.mission import Mission, MissionOutcome
from houston.util import TimeoutError, printflush
from houston.action import ActionOutcome


class Sandbox(object):
    """
    Sandboxes are used to provide an isolated, idempotent environment for
    executing test cases on a given system.
    """
    def __init__(self, system: 'System') -> None:
        self.__lock = threading.Lock()
        self.__system = system
        self.__bugzoo = system.snapshot.provision()

    @property
    def system(self) -> 'System':
        """
        The system under test by this sandbox.
        """
        return self.__system
    sut = system

    @property
    def bugzoo(self) -> Optional[bugzoo.Container]:
        """
        The BugZoo container underlying this sandbox.
        """
        return self.__bugzoo

    @property
    def alive(self) -> bool:
        """
        A flag indicating whether or not this sandbox is alive.
        """
        return self.__bugzoo is not None and self.__bugzoo.alive

    def _start(self, mission: Mission) -> None:
        """
        Starts a new SITL instance inside this sandbox.
        """
        raise NotImplementedError

    def _stop(self) -> None:
        """
        Stops the SITL running inside this sandbox.
        """
        raise NotImplementedError

    def run(self, mission: Mission) -> MissionOutcome:
        """
        Executes a given mission.
        """
        assert self.alive
        self.__lock.acquire()
        try:
            time_before_setup = timer()
            print('Setting up...'),
            self._start(mission)
            print('Setup complete.')
            setup_time = timer() - time_before_setup

            env = mission.environment
            outcomes = []

            # execute each action in sequence
            for action in mission.actions:
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
                printflush('Taking branch: {}\n'.format(branch))

                # enforce a timeout
                timeout = schema.timeout(self.system,
                                         action,
                                         state_before,
                                         env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                time_before = timer()
                passed = False
                try:
                    # TODO: dispatch to this container!
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
                    signal.alarm(0)

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
        if self.__bugzoo is not None:
            self.__bugzoo.destroy()
            self.__bugzoo = None
    delete = destroy

    def observe(self, running_time) -> None:
        """
        Returns an observation of the current state of the system running
        inside this sandbox.
        """
        assert self.alive
        vals = {n: v.read(self) for (n, v) in self.system.variables.items()}
        return State(vals, running_time)
