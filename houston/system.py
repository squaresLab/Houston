import bugzoo
import copy
import time
import timeit
import signal
import math

from houston.sandbox import Sandbox
from houston.mission import Mission, MissionOutcome
from houston.action import ActionSchema, ActionOutcome, Action
from houston.branch import BranchID, Branch, BranchPath
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

    def provision(self) -> Sandbox:
        """
        Constructs an interactive, ephemeral sandbox for this system.
        """
        return Sandbox(self)

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
