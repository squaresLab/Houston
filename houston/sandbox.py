import bugzoo
import threading
from typing import Optional
from houston.system import System


class Sandbox(object):
    """
    Sandboxes are used to provide an isolated, idempotent environment for
    executing test cases on a given system.
    """
    def __init__(self, system: System) -> None:
        self.__lock = threading.Lock()
        self.__system = system
        self.__bugzoo = system.snapshot.provision()

    @property
    def system(self) -> System:
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

    def _start(self) -> None:
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
            self._start()

            # TODO: run mission

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
