"""
TODO: module description
"""
import houston.state
import random

from houston.util import printflush
from houston.valueRange import ValueRange


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

    def __init__(self, name, parameters, branches):
        """
        Constructs an ActionSchema object.

        Args:
            name (str): name of the action schema
            parameters (list of Parameter): a list of the parameters for this
                action schema
            branches (list of Branch): a list of the possible outcomes for
                actions belonging to this schema.

        """
        from houston.branch import Branch

        assert isinstance(name, str)
        assert (len(name) > 0)
        assert isinstance(parameters, list)
        assert all(isinstance(p, Parameter) for p in parameters)
        assert isinstance(branches, list)
        assert all(isinstance(b, Branch) for b in branches)
        assert (len(branches) > 0)

        # unique branch names
        assert (len(set(b.name for b in branches)) == len(branches))

        self.__name = name
        self.__parameters =  parameters
        self.__branches = branches


    @property
    def name(self):
        """
        The name of this schema.
        """
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


    def dispatch(self, system, action, state, environment):
        """
        Responsible for invoking an action belonging to this schema.

        Args:
            system (System): the system under test
            action (Action): the action that is to be dispatched
            state (State): the state of the system immediately prior to the
                call to this method
            environment (Environment): a description of the environment in
                which the action is being performed
        """
        raise UnimplementedError


    def timeout(self, system, action, state, environment):
        """
        Responsible for calculating the maximum time that this action shoud take.

        :param  action          the action that is going to be performed.
        :param  state           the state in which the system is currently on.
        :param  environment     the system environment

        :returns maximum time in seconds (as a float)
        """
        branch = self.resolve_branch(system, action, state, environment)
        return branch.timeout(system, action, state, environment)


    @property
    def parameters(self):
        """
        A list of the parameters used to describe actions belonging to this schema.
        """
        return self.__parameters[:]


    def resolve_branch(self, system, action, initial_state, environment):
        """
        Returns the branch that is appropiate for the current action, state, and
        environment based on the current action schema.
        """
        for b in self.__branches:
            if b.precondition(system, action, initial_state, environment):
                return b
        raise Exception("failed to resolve branch")


    def generate(self, rng):
        """
        Generates an action belonging to this schema at random.
        """
        assert (isinstance(rng, random.Random) and rng is not None)
        values = {p.name: p.generate(rng) for p in self.__parameters}
        return Action(self.__name, values)


class ActionOutcome(object):
    @staticmethod
    def from_json(jsn):
        """
        TODO: add comment
        """
        from houston.branch import BranchID
        from houston.state import State

        assert isinstance(jsn, dict)
        assert ('successful' in jsn)
        assert ('action' in jsn)
        assert ('start_state' in jsn)
        assert ('end_state' in jsn)
        assert ('time_elapsed' in jsn)
        assert ('branch_id' in jsn)
        assert (isinstance(jsn['branch_id'], str) or isinstance(jsn['branch_id'], unicode))
        assert (jsn['branch_id'] != '')
        assert isinstance(jsn['successful'], bool)

        return ActionOutcome(Action.from_json(jsn['action']),
                             jsn['successful'],
                             State.from_json(jsn['start_state']),
                             State.from_json(jsn['end_state']),
                             jsn['time_elapsed'],
                             BranchID.from_json(jsn['branch_id']))


    """
    Used to describe the outcome of an action execution in terms of system state.
    """
    def __init__(self, action, successful, start_state, end_state, time_elapsed, branch_id):
        from houston.state import State
        from houston.branch import BranchID

        assert isinstance(action, Action)
        assert isinstance(successful, bool)
        assert isinstance(start_state, State)
        assert isinstance(end_state, State)
        assert isinstance(time_elapsed, float)
        assert isinstance(branch_id, BranchID)

        self.__action      = action
        self.__successful  = successful
        self.__start_state = start_state
        self.__end_state = end_state
        self.__time_elapsed = time_elapsed
        self.__branch_id = branch_id


    def to_json(self):
        """
        Returns a JSON description of this action outcome.
        """
        return {
            'action':       self.__action.to_json(),
            'successful':   self.__successful,
            'start_state':  self.start_state.to_json(),
            'end_state':    self.end_state.to_json(),
            'time_elapsed': self.__time_elapsed,
            'branch_id':    self.__branch_id.to_json()
        }

    
    @property
    def branch_id(self):
        """
        Returns an identifier for the branch that was taken by this action.
        """
        return self.__branch_id


    @property
    def passed(self):
        """
        Returns true if this action was successful.
        """
        return self.__successful

    
    @property
    def failed(self):
        """
        Returns true if this action was unsuccessful.
        """
        return not self.__successful


    @property
    def start_state(self):
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

    def __init__(self, schema_name, parameters = []):
        """
        Constructs a new action generator.

        :param  schemaName: the name of the schema for which this generator \
                    produces actions.
        :params parameters: a list of the parameters to this generator.
        """
        assert isinstance(schema_name, str)
        assert isinstance(parameters, list)

        self.__schema_name = schema_name
        self.__parameters = parameters


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

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError


    @property
    def schema_name(self):
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
