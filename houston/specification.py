from typing import List, Dict, Any
import sexpdata
import z3

from houston.action import ActionSchema, Parameter
from houston.state import State, Environment
#from houston.system import System

class InvalidExpression(Exception):
    pass

class Specification():

    def __init__(self, parameters: List[Parameter], precondition: str, postcondition: str, timeout: str):


        self._parameters = parameters
        self._precondition = Expression(precondition, parameters)
        self._postcondition = Expression(postcondition, parameters)
        self._timeout = timeout
        super().__init__()

    @property
    def precondition(self):
        return self._precondition

    @property
    def postcondition(self):
        return self._postcondition

    def timeout(self):
        # TODO fix this
        return self._system.constant_timeout_offset


class Expression:

    def __init__(self, s_expression: str, parameters: List[Parameter]):

        if not Expression.is_valid(s_expression):
            raise InvalidExpression

        self._expression = s_expression
        self._parameters = parameters

    @staticmethod
    def is_valid(string: str):
        try:
            parsed = sexpdata.loads(string)
        except (sexpdata.ExpectClosingBracket, sexpdata.ExpectNothing) as e:
            return False
        return True

    def is_satisfied(self, system: 'System', parameter_values: Dict[str, Any], state_before: State,
                    state_after: State, environment: Environment) -> bool:
        s = z3.Solver()
        smt = self._prepare_query(system, parameter_values, state_before, state_after)
        smt += self._expression
        print("AAAA " + smt)
        s.from_string(smt)

        return s.check() == z3.sat

    def _prepare_query(self, system: 'System', parameter_values: Dict[str, Any], state_before: State, state_after: State=None):
        smt = self._get_declarations(system)
        smt += Expression._values_to_smt('$', parameter_values)
        smt += Expression._values_to_smt('_', state_before.values)
        if state_after:
            smt += Expression._values_to_smt('__', state_before.values)
        return smt

    def _get_declarations(self, system):
        declarations = ""

        # Declare all parameters
        for p in self._parameters:
            typ = "Int"
            if p.type() == float:
                typ = "Real"
            elif p.type() == bool:
                typ = "Bool"
            declarations += "(declare-const ${} {})\n".format(p.name, typ)

        # Declare all state variables
        for n, v in system.variables.items():
            declarations += "(declare-const _{0} {1})\n(declare-const __{0} {1})\n".format(n, "Bool") # TODO right now we don't have a way to find out the type of state variables

        return declarations

    @staticmethod
    def _values_to_smt(prefix: str, values: Dict[str, Any]) -> str:
        smt = ""
        for n, v in values.items():
            smt += "(assert (= {}{} {}))\n".format(prefix, n, str(v).lower())
        return smt

    def is_satisfiable(self, system: 'System', state: State, environment: Environment) -> bool:
        s = z3.Solver()
        smt = self._get_declarations(system)
        smt += Expression._values_to_smt('_', state.values)
        smt += self._expression
        s.from_string(smt)

        return s.check() == z3.sat
