__all__ = ['System']

from typing import List
import copy
import time
import timeit
import signal
import math

import bugzoo

from .sandbox import Sandbox
from .mission import Mission, MissionOutcome
from .action import ActionSchema, ActionOutcome, Action
from .branch import BranchID, Branch, BranchPath
from .state import Variable


class System(object):
    """
    Instances of the System class are used to provide a description of a
    system-under-test, and to provide an interface for safely interacting
    with the system-under-test in an idempotent manner.
    """
    def __init__(self,
                 bug_name: str,
                 variables: List[Variable],
                 schemas: List[ActionSchema]
                 ) -> None:
        self.__bugzoo = bugzoo.BugZoo()
        self.__snapshot = self.__bugzoo.bugs[bug_name]
        self.__bugzoo.bugs.build(self.__snapshot)
        self.__variables = {v.name: v for v in variables}
        self.__schemas = {s.name: s for s in schemas}

    def provision(self) -> Sandbox:
        """
        Constructs an interactive, ephemeral sandbox for this system.
        """
        raise NotImplementedError

    @property
    def bugzoo(self):
        """
        The BugZoo daemon.
        """
        return self.__bugzoo

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
        schema = self.__schemas[iden.schema_name]
        return schema.get_branch(iden)

    def variable(self, v: str) -> Variable:
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
