from typing import List, Dict, Any
from sexpdata import loads, dumps
from z3 import Solver, sat

from houston.action import ActionSchema, Parameter
from houston.state import State, Environment
#from houston.system import System

class InvalidExpression(Exception):
    pass

class Specification():

    def __init__(self, parameters: List[Parameter], precondition: str, postcondition: str, timeout: str):
        
        if not (Specification.is_expression_valid(precondition) and Specification.is_expression_valid(postcondition)):
            raise InvalidExpression()
        
        self._parameters = parameters
        self._precondition = precondition
        self._postcondition = postcondition
        self._timeout = timeout
        super().__init__()

    def is_precondition_satisfied(self, system: 'System', parameter_values: Dict[str, Any], state: State, environment: Environment) -> bool:
        s = Solver()
        smt = self._prepare_query(system, parameter_values, state)
        smt += self._precondition
        s.from_string(smt)

        if s.check() == sat:
            return True
        else:
            return False


    def is_postcondition_satisfied(self, system: 'System', parameter_values: Dict[str, Any], state_before: State,
                                    state_after: State, environment: Environment) -> bool:
        s = Solver()
        smt = self._prepare_query(system, parameter_values, state_before, state_after)
        smt += self._postcondition
        s.from_string(smt)

        if s.check() == sat:
            return True
        else:
            return False

    def timeout(self):
        # TODO fix this
        return self._system.constant_timeout_offset

    def is_satisfiable(self, system: 'System', state: State, environment: Environment) -> bool:
        s = Solver()
        smt = self._get_declarations(system)
        smt += Specification._values_to_smt('_', state_before.values)
        smt += self._precondition
        s.from_string(smt)

        if s.check() == sat:
            return True
        else:
            return False

    @staticmethod
    def is_expression_valid(string: str):
        try:
            parsed = loads(string)
        except Exception:
            return False
        return True

    def _prepare_query(self, system: 'System', parameter_values: Dict[str, Any], state_before: State, state_after: State=None):
        smt = self._get_declarations(system)
        smt += Specification._values_to_smt('$', parameter_values)
        smt += Specification._values_to_smt('_', state_before.values)
        if state_after:
            smt += Specification._values_to_smt('__', state_before.values)
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
    def values_to_smt(prefix: str, values: Dict[str, Any]) -> str:
        smt = ""
        for n, v in values.items():
            smt += "(assert (= {}{} {}))\n".format(prefix, n, str(v).lower())
        return smt
