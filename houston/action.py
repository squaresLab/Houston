from typing import List, Dict, Any, Optional
import random

from .state import State, Environment
from .util import printflush
from .valueRange import ValueRange


class Action(object):
    """
    Description of the concept of "Actions".
    """
    @staticmethod
    def from_json(jsn):
        """
        Constructs an Action object from its JSON description.
        """
        assert isinstance(jsn, dict)
        assert ('kind' in jsn)
        assert ('parameters' in jsn)
        return Action(jsn['kind'], jsn['parameters'])

    def __init__(self, kind, values):
        """
        Constructs an Action description.

        Args:
            kind    (str):  the name of the schema to which the action belongs
            values  (dict): a dictionary of parameter values for the action
        """
        assert (isinstance(kind, str) or isinstance(kind, unicode))
        assert isinstance(values, dict)
        self.__kind = kind
        self.__values = values.copy()

    @property
    def schema_name(self):
        """
        The name of the schema to which this action belongs.
        """
        return self.__kind

    def __getitem__(self, param):
        """
        Returns the value for a specific parameter in this action.
        """
        return self.__values[param]

    @property
    def values(self):
        """
        Returns a copy of the parameter values used by this action.
        """
        return self.__values.copy()

    def to_json(self):
        """
        Returns a JSON description of this action.
        """
        return {
            'kind': self.__kind,
            'parameters': self.values
        }


class Parameter(object):
    """
    Docstring.
    """
    def __init__(self, name, value_range):
        """
        Constructs a Parameter object.

        Args:
            name (str):                 the name of this parameter.
            value_range (ValueRange):   the range of possible values for this
                parameter, given as a ValueRange object.
        """
        # TODO: type checking
        assert (isinstance(name, str) or isinstance(name, unicode))
        assert isinstance(value_range, ValueRange)
        self.__name = name
        self.__value_range = value_range

    @property
    def values(self):
        """
        The range of possible values for this parameter.
        """
        return self.__value_range

    def generate(self, rng):
        """
        Returns a randomly-generated value for this parameter.
        """
        assert (isinstance(rng, random.Random) and rng is not None)
        return self.__value_range.sample(rng)

    @property
    def type(self):
        """
        The underlying type of this parameter.
        """
        return self.__value_range.type

    @property
    def name(self):
        """
        The name of this parameter.
        """
        return self.__name


class ActionSchema(object):
    """
    Action schemas are responsible for describing the kinds of actions that
    can be performed within a given system. Action schemas describe actions
    both syntactically, in terms of parameters, and semantically, in terms of
    preconditions, postconditions, and invariants.
    """
    def __init__(self,
                 name: str,
                 parameters: List[Parameter],
                 branches: 'List[Branch]'
                 ) -> None:
        """
        Constructs an ActionSchema object.

        Parameters:
            name: name of the action schema.
            parameters: a list of the parameters for this action schema.
            branches: a list of the possible outcomes for actions belonging to
                this schema.
        """
        from houston.branch import Branch  # FIXME this is awful

        assert len(name) > 0
        assert len(branches) > 0

        # unique branch names
        assert (len(set(b.name for b in branches)) == len(branches))

        self.__name = name
        self.__parameters = parameters
        self.__branches = branches

    @property
    def name(self) -> str:
        return self.__name

    @property
    def branches(self):
        """
        A list of the branches for this action schema.
        """
        return self.__branches[:]

    def get_branch(self, iden):
        """
        Returns a branch belonging to this action schema using its identifier.
        """
        from houston.branch import BranchID

        assert (isinstance(iden, BranchID) and iden is not None)
        assert (iden.get_action_name() == self.__name)
        return self.__branches[iden.get_branch_name()]

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment
                 ) -> None:
        """
        Responsible for invoking an action belonging to this schema.

        Args:
            sandbox: the sandbox for the system under test.
            action: the action that is to be dispatched.
            state: the state of the system immediately prior to the
                call to this method
            environment (Environment): a description of the environment in
                which the action is being performed
        """
        raise UnimplementedError

    def timeout(self,
                system: 'System',
                action: Action,
                state: State,
                environment: Environment
                ) -> float:
        """
        Responsible for calculating the maximum time that a given action
        should take to finish its execution.

        Parameters:
            system: the system under test.
            action: the action.
            state: the state of the system prior to the execution of the
                action.
            environment: the state of the environment prior to the execution
                of the action.

        Returns:
            Maximum length of time (in seconds) that the action may take to
            complete its execution.
        """
        branch = self.resolve_branch(system, action, state, environment)
        return branch.timeout(system, action, state, environment)

    # FIXME replace with frozenset
    @property
    def parameters(self) -> List[Parameter]:
        return self.__parameters[:]

    def resolve_branch(self,
                       system: 'System',
                       action: Action,
                       initial_state: State,
                       environment: Environment
                       ) -> 'Branch':
        """
        Returns the branch of this action schema that will be taken for a
        given action, state, and environment.
        """
        for b in self.__branches:
            if b.precondition(system, action, initial_state, environment):
                return b
        raise Exception("failed to resolve branch")

    def generate(self, rng: random.Random) -> Action:
        """
        Randomly generates an action belonging to this schema.
        """
        assert (isinstance(rng, random.Random) and rng is not None)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        return Action(self.__name, values)


class ActionOutcome(object):
    """
    Describes the outcome of a command execution in terms of the state of the
    system before and after the execution.
    """
    @staticmethod
    def from_json(jsn: Dict[str, Any]) -> 'ActionOutcome':
        from houston.branch import BranchID
        from houston.state import State
        return ActionOutcome(Action.from_json(jsn['action']),
                             jsn['successful'],
                             State.from_json(jsn['start_state']),
                             State.from_json(jsn['end_state']),
                             jsn['time_elapsed'],
                             BranchID.from_string(jsn['branch_id']))

    def __init__(self,
                 action: Action,
                 successful: bool,
                 start_state: State,
                 end_state: State,
                 time_elapsed: float,
                 branch_id: 'BranchID'  # FIXME
                 ) -> None:
        from houston.branch import BranchID
        self.__action = action
        self.__successful = successful
        self.__start_state = start_state
        self.__end_state = end_state
        self.__time_elapsed = time_elapsed
        self.__branch_id = branch_id

    def to_json(self) -> Dict[str, Any]:
        return {
            'action':       self.__action.to_json(),
            'successful':   self.__successful,
            'start_state':  self.start_state.to_json(),
            'end_state':    self.end_state.to_json(),
            'time_elapsed': self.__time_elapsed,
            'branch_id':    str(self.__branch_id)}

    @property
    def branch_id(self) -> str:
        return self.__branch_id

    @property
    def passed(self) -> bool:
        return self.__successful

    @property
    def failed(self) -> bool:
        return not self.__successful

    @property
    def start_state(self) -> State:
        """
        A description of the state of the system immediately after the
        execution of this action.
        """
        return self.__start_state

    @property
    def end_state(self):
        """
        A description of the state of the system immediately before the
        execution of this action.
        """
        return self.__end_state


class ActionGenerator(object):
    def __init__(self,
                 schema_name: str,
                 parameters: Optional[List[Parameter]] = None
                 ) -> None:
        """
        Constructs a new action generator.

        Parameters:
            schema_name: the name of the schema used by the actions produced
                by this generator.
            parameters: a list of parameters to this generator.
        """
        self.__schema_name = schema_name
        self.__parameters = parameters if parameters else []

    def construct_with_state(self, system, current_state, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError

    def construct_without_state(self, system, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        Returns:
            A dictionary of arguments for the generated action
        """
        raise NotImplementedError

    @property
    def schema_name(self) -> str:
        """
        The name of the schema to which actions generated by this
        generator belong.
        """
        return self.__schema_name

    def generate_action_with_state(self, system, current_state, env, rng):
        assert isinstance(rng, random.Random)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        values = self.construct_with_state(system, current_state, env, values)
        return Action(self.__schema_name, values)

    def generate_action_without_state(self, system, env, rng):
        assert isinstance(rng, random.Random)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        values = self.construct_without_state(system, env, values)
        return Action(self.__schema_name, values)
