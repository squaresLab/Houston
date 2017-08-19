import branch
import state

class Action(object):
    """
    Description of the concept of "Actions".
    """

    @staticmethod
    def fromJSON(jsn):
        """
        Constructs an Action object from its JSON description.
        """
        assert (isinstance(jsn, dict) and not jsn is None)
        assert ('kind' in jsn)
        assert ('parameters' in jsn)
        return Action(jsn['kind'], jsn['parameters'])


    def __init__(self, kind, values):
        """
        Constructs an Action description.

        :param  kind    the name of the schema to which the action belongs
        :param  values  a dictionary of parameter values for the action
        """
        assert ((isinstance(kind, str) or (isinstance(kind, unicode))) and not kind is None)
        assert (isinstance(values, dict) and not values is None)
        self.__kind = kind
        self.__values = values[:]


    def getSchemaName(self):
        """
        Returns the name of the schema to which this action belongs.
        """
        return self.__kind


    def read(self, value):
        """
        Returns the value for a specific parameter in this action.
        """
        return self.getValue(value)


    def getValue(self, value):
        """
        Returns the value for a specific parameter in this action.
        """
        return self.__values[value]


    def getValues(self):
        """
        Returns a copy of the parameters for this action.
        """
        return self.__values.copy()


    def toJSON(self):
        """
        Returns a JSON description of this action.
        """
        return {
            'kind': self.__kind,
            'parameters': self.getValues()
        }


class Parameter(object):
    """
    Docstring.
    """

    def __init__(self, name, valueRange, description='N/A'):
        """
        Constructs a Parameter object.

        :param  name:           the name of this parameter
        :param  valueRange:     the range of possible values for this parameter,\
                                given as a ValueRange object.
        :param  description:    a short description of the parameter
        """
        # TODO: type checking
        self.__name = name
        self.__valueRange = valueRange
        self.__description = description


    def getValueRange(self):
        """
        Returns the range of possible values for this parameter.
        """
        return self.__valueRange


    def generate(self):
        """
        Returns a sample (random)
        """
        return self.__valueRange.sample()


    def getType(self):
        """
        Returns the type of this parameter
        """
        return self.__valueRange.getType()


    def getDescription(self):
        """
        Returns a description of this parameter
        """
        return self.__description


    def getName(self):
        """
        Returns the name of this parameter.
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

        :param  name            name of the action schema
        :param  parameters      a list of the parameters for this action schema
        :param  branches        a list of the possible outcomes for actions \
                                belonging to this schema. If none of the \

        """
        assert (isinstance(name, str) and not name is None)
        assert (len(name) > 0)
        assert (isinstance(parameters, list) and not parameters is None)
        assert (all(isinstance(p, Parameter) for p in parameters))
        assert (isinstance(branches, list) and not branches is None)
        assert (all(isinstance(b, branch.Branch) for b in branches))
        assert (len(branches) > 0)

        # unique branch names
        assert (len(set(b.getName() for b in branches)) == len(branches))

        self.__name = name
        self.__parameters =  parameters
        self.__branches = branches


    def getName(self):
        """
        Returns the name of this schema.
        """
        return self.__name


    def getBranches(self):
        """
        Returns a list of the branches for this action schema.
        """
        return self.__branches[:]

    
    def getBranch(self, iden):
        """
        Returns a branch belonging to this action schema using its identifier.
        """
        assert (isinstance(iden, branch.BranchID) and iden is not None)
        assert (iden.getActionName() == self.__name)
        return self.__branches[iden.getBranchName()]


    def dispatch(self, action, state, environment):
        """
        Responsible for invoking an action belonging to this schema.

        :param  action  an Action belonging to this schema
        """
        raise UnimplementedError


    def computeTimeout(self, action, state, environment):
        """
        Responsible for calculating the maximum time that this action shoud take.

        :param  action          the action that is going to be performed.
        :param  state           the state in which the system is currently on.
        :param  environment     the system environment

        :returns maximum time in seconds (as a float)
        """
        branch = self.resolveBranch(action, state, environment)
        return branch.computeTimeout(action, state, environment)


    def getParameters(self):
        """
        Returns the parameters being hold for the current action schema. This is
        used to generate actions
        """
        return self.__parameters[:]


    def resolveBranch(self, action, initialState, environment):
        """
        Returns the branch that is appropiate for the current action, state, and
        environment based on the current action schema.
        """
        for b in self.__branches:
            if b.isApplicable(action, initialState, environment):
                return b
        raise Exception("failed to resolve branch")


    def generate(self):
        """
        Generates an action belonging to this schema at random.
        """
        values = {p.getName(): p.generate() for p in self.__parameters}
        return Action(self.__name, values)


class ActionOutcome(object):
    @staticmethod
    def fromJSON(jsn):
        """
        TODO: add comment
        """
        assert (isinstance(jsn, dict) and not jsn is None)
        assert ('successful' in jsn)
        assert ('action' in jsn)
        assert ('stateBefore' in jsn)
        assert ('stateAfter' in jsn)
        assert ('timeElapsed' in jsn)
        assert ('branchID' in jsn)
        assert (isinstance(jsn['branchID'], str) and not jsn['branchID'] is None)
        assert (jsn['branchID'] != '')
        assert (isinstance(jsn['successful'], bool) and not jsn['successful'] is None)

        return ActionOutcome(Action.fromJSON(jsn['action']),
                             jsn['successful'],
                             state.State.fromJSON(jsn['stateBefore']),
                             state.State.fromJSON(jsn['stateAfter']),
                             jsn['timeElapsed'],
                             branch.BranchID(jsn['branchID']))


    """
    Used to describe the outcome of an action execution in terms of system state.
    """
    def __init__(self, action, successful, stateBefore, stateAfter, timeElapsed, branchID):
        """
        Constructs a ActionOutcome.

        :param  action      the action that was performed
        :param  succesful   a flag indicating if the action was completed \
                            successfully
        :param  stateBefore the state of the system immediately prior to execution
        :param  stateAfter  the state of the system immediately after execution
        :param  branchID    the identifier of the branch that was taken \
                            during the execution of this action
        """
        assert (isinstance(action, Action) and not action is None)
        assert (isinstance(successful, bool) and not successful is None)
        assert (isinstance(stateBefore, state.State) and not stateBefore is None)
        assert (isinstance(stateAfter, state.State) and not stateAfter is None)
        assert (isinstance(timeElapsed, float) and not timeElapsed is None)
        assert (isinstance(branchID, branch.BranchID) and not branchID is None)

        self.__action      = action
        self.__successful  = successful
        self.__stateBefore = stateBefore
        self.__stateAfter  = stateAfter
        self.__timeElapsed = timeElapsed
        self.__branchID = branchID


    def toJSON(self):
        """
        Returns a JSON description of this action outcome.
        """
        return {
            'action':       self.__action.toJSON(),
            'successful':   self.__successful,
            'stateBefore':  self.__stateBefore.toJSON(),
            'stateAfter':   self.__stateAfter.toJSON(),
            'timeElapsed':  self.__timeElapsed,
            'branchID':     self.__branchID.toJSON()
        }

    
    def getBranchID(self):
        """
        Returns an identifier for the branch that was taken by this action.
        """
        return self.__branchID


    def passed(self):
        """
        :see `successful`
        """
        return self.successful()


    def successful(self):
        """
        Returns true if this action was unsuccessful.
        """
        return self.__successful


    def failed(self):
        """
        Returns true if this action was unsuccessful.
        """
        return not self.__successful


    def getEndState(self):
        """
        Returns a description of the state of the system immediately after the
        execution of this action.
        """
        return self.__stateAfter


    def getStartState(self):
        """
        Returns a description of the state of the system immediately before the
        execution of this action.
        """
        return self.__startBefore
