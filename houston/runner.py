from typing import Optional

import threading
import time
import signal
from bugzoo.client import Client as BugZooClient

from .util import TimeoutError, printflush
from .mission import Mission


class MissionRunner(threading.Thread):
    """
    Mission runners are used to continually fetch pending tests from an
    associated pool, and to execute those tests.
    """
    def __init__(self,
                 pool,
                 bz: BugZooClient,
                 snapshot_name: str,
                 with_coverage: bool = False
                 ) -> None:
        super().__init__()
        self.daemon = True
        self.__pool = pool
        self.__with_coverage = with_coverage
        self.__bz = bz
        self.__snapshot_name = snapshot_name

    def run(self) -> None:
        """
        Continues to process jobs.
        """
        while True:
            m = self.__pool.fetch()
            if m is None:
                return

            if self.__with_coverage:
                # FIXME
                raise NotImplementedError
            else:
                outcome = m.run(self.__bz, self.__snapshot_name)
                coverage = None
            self.__pool.report(m, outcome, coverage)

    def shutdown(self):
        if self.__sandbox is not None:
            self.__sandbox.destroy()
            self.__sandbox = None


class MissionRunnerPool(object):
    """
    Mission runner pools are used to distribute the execution of a stream
    of missions across a given number of workers, each running on a separate
    thread.
    """
    def __init__(self,
                 bz: BugZooClient,
                 snapshot_name: str,
                 system: 'System',
                 size: int,
                 source,  # FIXME
                 callback,  # FIXMe
                 with_coverage=False):
        assert callable(callback)
        assert size > 0

        # if a list is provided, use an iterator for that list
        if isinstance(source, list):
            source = iter(source)

        self.__system = system
        self.__source = source
        self.__callback = callback
        self._lock = threading.Lock()

        # provision desired number of runners
        self.__runners = \
            [MissionRunner(self, bz, snapshot_name, with_coverage)
                for _ in range(size)]

    def run(self) -> None:
        """

        """
        try:
            for runner in self.__runners:
                runner.start()

            # soft block until all runners have finished
            # (unlike join, we allow exceptions to be thrown to the parent
            #  thread)
            while True:
                if not any(runner.is_alive() for runner in self.__runners):
                    break
                time.sleep(0.1)

        finally:
            self.shutdown()

    def shutdown(self) -> None:
        """
        Kills all runners that belong to this pool.
        """
        if self.__runners == []:
            return

        for runner in self.__runners:
            if runner is not None:
                runner.shutdown()
        self.__runners = []

    @property
    def system(self) -> 'System':
        """
        The system under test.
        """
        return self.__system

    @property
    def size(self) -> int:
        """
        The number of independent threads being used by the pool to run
        tests.
        """
        return self.__runners.length()

    def report(self, mission, outcome, coverage=None) -> None:
        """
        Used to report the outcome of a mission.

        WARNING: It is the responsibility of the callback to guarantee
            thread safety (if necessary).
        """
        self.__callback(mission, outcome, coverage)

    def fetch(self) -> Optional[Mission]:
        """
        Returns the next mission from the (lazily-generated) queue, or None if
        there are no missions left to run.

        This method is considered to be thread safe (no concurrent reads from
        the source of the pool are allowed).
        """
        # acquire fetch lock
        self._lock.acquire()
        try:
            return self.__source.__next__()

        except StopIteration:
            return None

        finally:
            self._lock.release()
