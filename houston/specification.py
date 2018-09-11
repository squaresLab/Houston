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
        #self._timeout = timeout
        self._timeout = 1.0
        super().__init__()

    @property
    def precondition(self):
        return self._precondition

    @property
    def postcondition(self):
        return self._postcondition

    @property
    def parameters(self):
        return self._parameters

    def timeout(self):
        # TODO fix this
        return self._timeout

    def get_constraint(self, state: State, postfix: str=''):
        smt = self._precondition.get_declarations(state, postfix)
        smt += "(assert {})\n".format(self._precondition.get_expression(state, postfix))
        smt += "(assert {})\n".format(self._postcondition.get_expression(state, postfix))

        return smt


class Expression:

    def __init__(self, s_expression: str, parameters: List[Parameter]):

        if not Expression.is_valid(s_expression):
            raise InvalidExpression

        self._expression = s_expression
        self._parameters = parameters

    @property
    def expression(self):
        return self._expression

    @staticmethod
    def is_valid(string: str):
        try:
            parsed = sexpdata.loads(string)
        except (sexpdata.ExpectClosingBracket, sexpdata.ExpectNothing) as e:
            return False
        return True

    def is_satisfied(self, system: 'System', parameter_values: Dict[str, Any], state_before: State,
                    state_after: State, environment: Environment) -> bool:
        s = z3.SolverFor("QF_NRA")
        smt = self._prepare_query(system, parameter_values, state_before, state_after)
        smt += "(assert {})".format(self._expression)
        print("SMT:\n" + smt)
        s.from_string(smt)

        print("Z3 result: " + str(s.check()))
        return s.check() == z3.sat

    def _prepare_query(self, system: 'System', parameter_values: Dict[str, Any], state_before: State, state_after: State=None):
        smt = self.get_declarations(state_before)
        smt += Expression.values_to_smt('$', parameter_values)
        smt += Expression.values_to_smt('_', state_before.values)
        if state_after:
            smt += Expression.values_to_smt('__', state_after.values)
        return smt

    def get_declarations(self, state: State, postfix: str=''):
        declarations = ""

        # Declare all parameters
        for p in self._parameters:
            declarations += "(declare-const ${}{} {})\n".format(p.name, postfix,
                        Expression._type_to_string(p.type))

        # Declare all state variables
        for n, v in state.values.items():
            declarations += "(declare-const _{0}{1} {2})\n(declare-const __{0}{1} {2})\n".format(n,
                        postfix, Expression._type_to_string(type(v))) # TODO right now we don't have a way to find out the type of state variables

        return declarations

    @staticmethod
    def _type_to_string(typ):
        t = "Int"
        if typ == float:
            t = "Real"
        elif typ == bool:
            t = "Bool"
        elif typ == str:
            t = "String"
        return t

    @staticmethod
    def values_to_smt(prefix: str, values: Dict[str, Any], postfix: str='') -> str:
        smt = ""
        for n, v in values.items():
            if type(v) == str:
                smt += "(assert (= {}{}{} \"{}\"))\n".format(prefix, n, postfix, v)
            elif type(v) == float:
                smt += "(assert (= {}{}{} {:.4f}))\n".format(prefix, n, postfix, v)
            else:
                smt += "(assert (= {}{}{} {}))\n".format(prefix, n, postfix, str(v).lower())
        return smt

    def is_satisfiable(self, system: 'System', state: State, environment: Environment) -> bool:
        s = z3.SolverFor("QF_NRA")
        smt = self.get_declarations(system)
        smt += Expression.values_to_smt('_', state.values)
        smt += "(assert {})".format(self._expression)
        s.from_string(smt)

        return s.check() == z3.sat

    def get_expression(self, state: State, postfix: str=''):
        expr = self._expression
        if not postfix:
            return expr

        for p in self._parameters:
            expr = expr.replace("${}".format(p.name), "${}{}".format(p.name, postfix))

        for n,v in state.values.items():
            expr = expr.replace("_{}".format(n), "_{}{}".format(n, postfix))

        return expr
