__all__ = ['System']

from typing import List, Dict, FrozenSet
import copy
import time
import timeit
import signal
import math
import warnings

import bugzoo
from bugzoo.core.bug import Bug as Snapshot

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
                 schemas: List[ActionSchema]
                 ) -> None:
        self.__bugzoo = bugzoo.BugZoo()
        self.__snapshot = self.__bugzoo.bugs[bug_name]
        self.__bugzoo.bugs.build(self.__snapshot)
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
        warnings.warn("System.bugzoo will soon be removed", DeprecationWarning)
        return self.__bugzoo

    @property
    def snapshot(self) -> Snapshot:
        """
        The snapshot, provided by BugZoo, used to provide access to a concrete
        implementation of this system (known as a "sandbox").
        """
        return self.__snapshot

    @property
    def branches(self) -> List[Branch]:
        """
        A list of the branches for this system.
        """
        return [b for s in self.__schemas.values() for b in s.branches]

    def branch(self, iden) -> Branch:
        """
        Returns an outcome branch for this system provided its identifier.
        """
        assert isinstance(iden, BranchID)
        schema = self.__schemas[iden.action_name]
        return schema.branch(iden)

    def variable(self, v: str) -> Variable:
        warnings.warn("System.variable will soon be removed",
                      DeprecationWarning)
        for variable in self.variables:
            if variable.name == v:
                return variable
        raise KeyError("unable to find variable: {}".format(v))

    @property
    def variables(self) -> FrozenSet[Variable]:
        warnings.warn("System.variables will soon be transformed into a class method",  # noqa: pycodestyle
                      DeprecationWarning)
        return self.__class__.state.variables

    @property
    def schemas(self) -> Dict[str, ActionSchema]:
        """
        Returns a copy of action schemas
        """
        warnings.warn("System.schemas will soon be removed",
                      DeprecationWarning)
        return copy.copy(self.__schemas)
