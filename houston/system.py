import copy
import json
import state
import mission
import timeit
import signal
import math

from branch import BranchID, Branch, BranchPath

from util import TimeoutError


class System(object):
    """
    Description of System.
    """


    def __init__(self, identifier, variables, schemas):
        """
        Constructs a new System.

        :param  identifier: a unique string identifier (i.e., a name) for this\
                            system
        :param  variables:  a dictionary of system variables, indexed by name
        :param  schemas:    a dictionary of action schemas, indexed by name
        """
        assert (isinstance(identifier, str) and not None)
        assert (isinstance(variables, dict) and not None)
        self.__identifier = identifier
        self.__variables = variables
        self.__schemas = schemas


    def installed(self):
        """
        Returns true if this system is installed on this machine.
        """
        raise NotImplementedError


    def getIdentifier(self):
        """
        Returns the unique identifier (i.e., the name) for this system.
        """
        return self.__identifier

   
    def getBranches(self):
        """
        Returns a list of the branches for this system.
        """
        return [b for s in s.__schemas for b in s.getBranches()]


    def getBranch(self, iden):
        """
        Returns an outcome branch for this sytem provided its identifier.
        """
        assert (isinstance(iden, BranchID) and iden is not None)
        schema = self.__schemas[iden.getActionName()]
        return schema.getBranch(iden)


    def setUp(self, mission):
        """
        Responsible for appropriately configuring and launching the system,
        for a given mission.
        """
        raise NotImplementedError


    def tearDown(self, mission):
        """
        Responsible for safely closing the system, following the execution of
        a given mission.
        """
        raise NotImplementedError


    def execute(self, msn):
        """
        Executes a given mission.

        :param  msn:    the mission that should be executed.

        :return A summary of the outcome of the mission, in the form of a
                MissionOutcome
        """
        assert (self.installed())
        timeBeforeSetup = timeit.default_timer()
        self.setUp(msn)
        totalSetupTime = timeit.default_timer() - timeBeforeSetup

        env = msn.getEnvironment()
        outcomes = []

        try:

            # execute each action in sequence
            for action in msn.getActions():
                schema = self.__schemas[action.getSchemaName()]

                # compute expected state
                initialState = self.getState()

                # resolve the branch and compute the expected outcome
                branch = schema.resolveBranch(action, initialState, env)
                expected = branch.computeExpectedState(action, initialState, env)

                # enforce a timeout
                timeout = schema.computeTimeout(action, initialState, env)
                signal.signal(signal.SIGALRM, lambda signum, frame: TimeoutError.produce())
                signal.alarm(int(math.ceil(timeout)))

                timeBefore = timeit.default_timer()

                try:
                    schema.dispatch(action, initialState, env)
                except TimeoutError:
                    pass
                finally:
                    signal.alarm(0) # does this reset the alarm?

                timeAfter = timeit.default_timer()
                timeElapsed = timeAfter - timeBefore

                print('Doing: {}'.format(action.getSchemaName()))

                # compare the observed and expected states
                observed = self.getState()
                passed = expected.isExpected(self.__variables, observed)
                outcome = mission.ActionOutcome(action, passed, initialState, observed, timeElapsed, branch.getID())
                outcomes.append(outcome)

                if not passed:
                    totalTime = timeit.default_timer() - timeBeforeSetup
                    return mission.MissionOutcome(False, outcomes, totalSetupTime, \
                                                                        totalTime)
            totalTime = timeit.default_timer() - timeBeforeSetup
            return mission.MissionOutcome(True, outcomes, totalSetupTime, totalTime)

        finally:
            self.tearDown(msn)


    def getState(self):
        """
        Returns a description of the current state of the system.

        TODO: ensure that the system is actually running!
        """
        assert (self.installed())
        vals = {n: v.read() for (n, v) in self.__variables.items()}
        return state.State(vals)


    def getActionSchemas(self):
        """
        Returns a copy of action schemas
        """
        return copy.deepcopy(self.__schemas)


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
        assert (all(isinstance(p, mission.Parameter) for p in parameters))
        assert (isinstance(branches, list) and not branches is None)
        assert (all(isinstance(b, OutcomeBranch) for b in branches))
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
        assert (isinstance(iden, BranchID) and iden is not None)
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
        return copy.deepcopy(self.__parameters)


    def resolveBranch(self, action, initialState, environment):
        """
        Returns the branch that is appropiate for the current action, state, and
        environment based on the current action schema.
        """
        branch = None
        for b in self.__branches:
            if b.isApplicable(action, initialState, environment):
                return b
        raise Exception


    def generate(self):
        """
        Generates an action belonging to this schema at random.
        """
        values = {p.getName(): p.generate() for p in self.__parameters}
        return mission.Action(self.__name, values)


class ActionGenerator(object):

    def __init__(self, schemaName, parameters = []):
        """
        Constructs a new action generator.

        :param  schemaName: the name of the schema for which this generator \
                    produces actions.
        :params parameters: a list of the parameters to this generator.
        """
        assert (isinstance(schemaName, str) and schemaName is not None)
        assert (isinstance(parameters, list) and parameters is not None)

        self.__schemaName = schemaName
        self.__parameters = parameters


    def constructWithState(self, currentState, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError


    def constructWithoutState(self, env, values):
        """
        Responsible for constructing a dictionary of Action arguments based
        on the current state of the robot, a description of the environment,
        and a dictionary of generator parameter values.

        :returns    a dictionary of arguments for the generated action
        """
        raise NotImplementedError


    def getSchemaName(self):
        """
        Returns the name of the schema to which actions generated by this
        generator belong.
        """
        return self.__schemaName


    def generateActionWithState(self, currentState, env):
        values = {p.getName(): p.generate() for p in self.__parameters}
        values = self.constructWithState(currentState, env, values)
        return mission.Action(self.__schemaName, values)


    def generateActionWithoutState(self, env):
        values = {p.getName(): p.generate() for p in self.__parameters}
        values = self.constructWithoutState(env, values)
        return mission.Action(self.__schemaName, values)
