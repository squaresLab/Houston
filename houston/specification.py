from typing import List, Dict, Any
import sexpdata
import z3

from .action import ActionSchema, Parameter
from .state import State
from .environment import Environment
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
        decls = self._precondition.get_declarations(state, postfix)
        smt = self._precondition.get_expression(decls)
        smt.extend(self._postcondition.get_expression(decls))

        return smt, decls


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
        smt, decls = self._prepare_query(system, parameter_values, state_before, state_after)
        expr = self.get_expression(decls)
        smt.extend(expr)
        print("SMT: {}".format(smt))
#        s.from_string(smt)
        s.add(smt)

        print("Z3 result: " + str(s.check()))
        return s.check() == z3.sat

    def _prepare_query(self, system: 'System', parameter_values: Dict[str, Any], state_before: State, state_after: State=None):
        decls = self.get_declarations(state_before)
        smt = Expression.values_to_smt('$', parameter_values, decls)
        smt.extend(Expression.values_to_smt('_', state_before.to_json(), decls))
        if state_after:
            smt.extend(Expression.values_to_smt('__', state_after.to_json(), decls))
        return smt, decls

    def get_declarations(self, state: State, postfix: str=''):
        declarations = {}

        # Declare all parameters
        for p in self._parameters:
            declarations['${}'.format(p.name)] = Expression._type_to_z3(p.type, '${}{}'.format(p.name, postfix))

        # Declare all state variables
        for n, v in state.to_json().items():
            declarations['_{}'.format(n)] = Expression._type_to_z3(type(v), '_{}{}'.format(n, postfix))
            declarations['__{}'.format(n)] = Expression._type_to_z3(type(v), '__{}{}'.format(n, postfix))
            # TODO right now we don't have a way to find out the type of state variables

        return declarations

    @staticmethod
    def _type_to_string(typ) -> str:
        t = "Int"
        if typ == float:
            t = "Real"
        elif typ == bool:
            t = "Bool"
        elif typ == str:
            t = "String"
        return t

    @staticmethod
    def _type_to_z3(typ, name):
        if typ == float:
            t = z3.Real(name)
        elif typ == bool:
            t = z3.Bool(name)
        elif typ == str:
            t = z3.String(name)
        else:
            t = z3.Int(name)
        return t


    @staticmethod
    def values_to_smt(prefix: str, values: Dict[str, Any], declarations: Dict[str, Any]) -> str:
        smt = []
        for n, v in values.items():
            if type(v) == str:
                smt.append(declarations['{}{}'.format(prefix, n)] == z3.StringVal(v))
            else:
                smt.append(declarations['{}{}'.format(prefix, n)] == v)
        return smt

    def is_satisfiable(self, system: 'System', state: State, environment: Environment) -> bool:
        s = z3.SolverFor("QF_NRA")
        decls = self.get_declarations(state)
        smt = Expression.values_to_smt('_', state.to_json(), decls)
        smt.extend(self.get_expression(decls))
#        s.from_string(smt)
        s.add(smt)

        return s.check() == z3.sat

    def get_expression(self, decls: Dict[str, Any]):
        expr = z3.parse_smt2_string('(assert {})'.format(self.expression), decls=decls)
        return list(expr)
