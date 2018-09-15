__all__ = ['System']

from typing import List, Dict, FrozenSet, Any
import warnings
import logging

import bugzoo
from bugzoo.client import Client as BugZooClient
from bugzoo.core.bug import Bug as Snapshot

from .configuration import Configuration
from .sandbox import Sandbox
from .mission import Mission, MissionOutcome
from .action import ActionSchema, ActionOutcome, Action
from .branch import BranchID, Branch, BranchPath
from .state import Variable, State

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class SystemMeta(type):
    def __new__(mcl,
                cls_name: str,
                bases,  # FIXME
                ns: Dict[str, Any]
                ):
        # is this an abstract class?
        if 'is_abstract' in ns:
            is_abstract = ns['is_abstract']
            if not isinstance(ns['is_abstract'], bool):
                typ = type(ns['is_abstract']).__name__
                msg = "expected 'bool' but was '{}'".format(typ)
                msg = \
                    "Unexpected type for 'is_abtract' property: {}".format(msg)
                raise TypeError(msg)
        else:
            is_abstract = False

        # construct an immutable "is_abstract" property
        ns['is_abstract'] = property(lambda self, v=is_abstract: v)

        if not is_abstract:
            if 'state' not in ns:
                msg = "System class definition is missing 'state' property"
                raise TypeError(msg)
            if not issubclass(ns['state'], State):
                typ = ns['state'].__name__
                msg = "was {} but should be a subclass of State".format(typ)
                msg = "Unexpected class for 'state' property: {}".format(msg)
                raise TypeError(msg)

            # if 'configuration' not in ns:
            #     msg = "System class definition is missing 'configuration' property"  # noqa: pycodestyle
            #     raise TypeError(msg)
            # if not issubclass(ns['configuration'], Configuration):
            #     msg = "was {} but should be a subclass of Configuration"
            #     msg = msg.format(ns['configuration'].__name__)
            #     tpl = "Unexpected class for 'configuration' property: {}"
            #     msg = tpl.format(msg)
            #     raise TypeError(msg)

        return super().__new__(mcl, cls_name, bases, ns)


class System(object, metaclass=SystemMeta):
    """
    Instances of the System class are used to provide a description of a
    system-under-test, and to provide an interface for safely interacting
    with the system-under-test in an idempotent manner.
    """
    is_abstract = True

    def __init__(self,
                 schemas: List[ActionSchema],
                 snapshot: Snapshot,
                 config: Configuration
                 ) -> None:
        # TODO do not allow instantiation of abstract classes
        self.__snapshot = snapshot
        self.__configuration = config
        # FIXME this should be a class variable
        self.schemas = {s.name: s for s in schemas}

    def provision(self, client_bugzoo: BugZooClient) -> Sandbox:
        """
        Constructs an interactive, ephemeral sandbox for this system.
        """
        raise NotImplementedError

    @property
    def configuration(self) -> Configuration:
        return self.__configuration

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

    def duration(self, mission: Mission) -> float:
        """
        Computes an estimate of the length of time required to finish
        executing a given mission.
        """
        # FIXME move to Mission.duration when circular dependencies are broken
        duration = 0.0
        for command in mission:
            schema = self.schemas[command.schema_name]
            timeout = schema.compute_timeout(command,
                                             mission.initial_state,
                                             mission.environment,
                                             self.configuration)
            duration += timeout
        return duration
