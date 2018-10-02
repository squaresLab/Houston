import time
import threading

from .base import TestGenerator
from ..test import Test, TestOutcome
from ..command import CommandOutcome, Command
from ..util import printflush


class TreeBasedTestGenerator(TestGenerator):
    def __init__(self,
                 system,
                 initial_state,
                 env,
                 threads=1,
                 action_generators=None,
                 max_num_actions=10):
        super().__init__(system, threads, action_generators, max_num_actions)
        self.__seed_test = Test(env, initial_state, [])
        self.__queue_lock = threading.Lock()

    @property
    def seed_test(self):
        """
        The test that is used as a seed when generating new tests.
        """
        return self.__seed_test

    def record_outcome(self, test, outcome):
        """
        Once the outcome of a test has been determined, this function is
        reponsible for guiding the generation of new tests based on the
        outcome of that test.

        If the test failed, it indicates that either:

            (a) there is either a bug in the system under test,
            (b) there is non-determinism in the outcome of tests, or
            (c) the system is poorly specified.

        If the test was successful, a new test is generated for each
        (reachable) child node in the behaviour graph.
        """
        super(TreeBasedTestGenerator, self).record_outcome(test, outcome)

        self.__queue_lock.acquire()
        try:
            intended_path = self.__intended_paths[test]
            del self.__intended_paths[test]
            if outcome.passed:
                self.expand(test)
            else:
                # TODO: should we prune both?
                # self.prune(intended_path)
                executed_path = self.executed_path(test)
                self.prune(executed_path)
        finally:
            self.__num_running -= 1
            self.__queue_lock.release()

    def prune(self, path: 'BranchPath') -> None:
        """
        Removes a given branch path from the search space, preventing further
        exploration along that path.
        """
        printflush("Adding path to tabu list: {}".format(path))  # FIXME

        def fltr(m: Test) -> bool:
            return not self.__intended_paths[m].startswith(path)

        self.__queue = set(filter(keep, self.__queue))

    def prepare(self, seed, resource_limits):
        super().prepare(seed, resource_limits)

        self.__intended_paths = {}
        self.__queue = set()
        self.__num_running = 0
        self.expand(self.seed_test)

    def cleanup(self):
        self.__queue = set()
        self.__num_running = 0

    def reduce(self):
        # toposort and retain leaves
        return super(TreeBasedTestGenerator, self).reduce()

    def exhausted(self):
        """
        The search is exhausted when either its resource limit has been hit, or
        there are no jobs running and no jobs queued (implying that the search
        space has been exhausted).
        """
        if super(TreeBasedTestGenerator, self).exhausted():
            return True
        return self.__queue == set() and self.__num_running == 0

    def generate_test(self):
        while not self.exhausted():
            self.__queue_lock.acquire()
            try:
                if self.__queue != set():
                    test = self.rng.sample(self.__queue, 1)[0]
                    self.__queue.remove(test)
                    self.__num_running += 1
                    return test
            finally:
                self.__queue_lock.release()

            # wait before checking the queue again
            time.sleep(0.05)
            self.tick()

        # if the search has been exhausted, stop generating more tests
        raise StopIteration

    def expand(self, test):
        """
        Called after a test has finished executing
        """
        state = self.end_state(test)
        env = test.environment
        path = self.executed_path(test)

        # if we've hit the action limit, don't expand
        has_max_actions = self.max_num_actions is not None
        if has_max_actions and self.max_num_actions == test.size:
            return

        # otherwise, explore each branch
        branches = self.system.branches
        branches = [b for b in branches
                    if b.is_satisfiable(self.system, state, env)]
        for b in branches:
            p = path.extended(b)
            a = self.generate_action(b, env, state)
            m = test.extended(a)
            self.__queue.add(m)
            self.__intended_paths[m] = p

    def generate_action(self, branch, env, state):
        """
        TODO: add branch-specific action generators
        """
        generator = self.action_generator(branch.schema)
        if generator is not None:
            g = generator.generate_action_with_state
            return g(self.system, state, env, self.rng)
        return branch.generate(self.system, state, env, self.rng)
