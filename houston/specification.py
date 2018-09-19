__all__ = ['Specification', 'Expression', 'Idle']

import logging
import random
import attr
import math
from typing import List, Dict, Any
import sexpdata
import z3

from .configuration import Configuration
from .state import State
from .environment import Environment
#from houston.system import System

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)

class InvalidExpression(Exception):
    pass

class Specification():

    def __init__(self, name: str, precondition: str, postcondition: str):

        self._name = name
        self._precondition = Expression(precondition)
        self._postcondition = Expression(postcondition)
        super().__init__()

    @property
    def precondition(self):
        return self._precondition

    @property
    def postcondition(self):
        return self._postcondition

    @property
    def name(self):
        return self._name

    def timeout(self, command: 'Command', state: State, environment: Environment,
        config: Configuration) -> float:
        # TODO fix this
        return 1.0

    def get_constraint(self, command: 'Command', state: State, postfix: str=''):
        decls = self._precondition.get_declarations(command, state, postfix)
        smt = self._precondition.get_expression(decls, state, postfix)
        smt.extend(self._postcondition.get_expression(decls, state, postfix))

        return smt, decls


class Expression:

    def __init__(self, s_expression: str):

        if not Expression.is_valid(s_expression):
            raise InvalidExpression

        self._expression = s_expression

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

    def is_satisfied(self, command: 'Command', state_before: State,
                    state_after: State, environment: Environment, config: Configuration) -> bool:
        logger.debug("Checking for command {}".format(command.__class__.__name__))
        s = z3.SolverFor("QF_NRA")
        smt, decls = self._prepare_query(command, state_before, state_after)
        expr = self.get_expression(decls, state_before)
        smt.extend(expr)
        logger.info("SMT: {}".format(smt))
#        s.from_string(smt)
        s.add(smt)

        logger.debug("Z3 result: " + str(s.check()))
        return s.check() == z3.sat

    def _prepare_query(self, command: 'Command', state_before: State, state_after: State=None):
        decls = self.get_declarations(command, state_before)
        smt = Expression.values_to_smt('$', command.to_json(), decls)
        smt.extend(Expression.values_to_smt('_', state_before.to_json(), decls))
        if state_after:
            smt.extend(Expression.values_to_smt('__', state_after.to_json(), decls))
        return smt, decls

    def get_declarations(self, command: 'Command', state: State, postfix: str=''):
        declarations = {}

        # Declare all parameters
        for p in command.parameters:
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

    def is_satisfiable(self, command: 'Command', state: State, environment: Environment) -> bool:
        s = z3.SolverFor("QF_NRA")
        decls = self.get_declarations(command, state)
        smt = Expression.values_to_smt('_', state.to_json(), decls)
        smt.extend(self.get_expression(decls, state))
#        s.from_string(smt)
        s.add(smt)

        return s.check() == z3.sat

    def get_expression(self, decls: Dict[str, Any], state: State, postfix: str=""):
        expr = list(z3.parse_smt2_string('(assert {})'.format(self.expression), decls=decls))
        variables = {}
        for v in state.variables:
            variables['_{}{}'.format(v.name, postfix)] = float(v.noise) if v.is_noisy else 0.0
            variables['__{}{}'.format(v.name, postfix)] = float(v.noise) if v.is_noisy else 0.0
        expr_with_noise = [Expression.recreate_with_noise(e, variables) for e in expr]
        return expr_with_noise

    @staticmethod
    def recreate_with_noise(expr: z3.ExprRef, variables: Dict[z3.ArithRef, float]):
        d = expr.decl()
        if str(d) != '==':
            children = [Expression.recreate_with_noise(c, variables) for c in expr.children()]
            #TODO find a better solution
            if str(d) == 'And':
                return z3.And(*children)
            elif str(d) == 'Or':
                return z3.Or(*children)
            return d(*children)
        lhs, rhs = expr.children()[0], expr.children()[1]
        if not isinstance(lhs, z3.ArithRef) or not isinstance(rhs, z3.ArithRef):
            return d(lhs, rhs)
        def absolute(x):
            return z3.If(x > 0, x, -x)
        return absolute(lhs - rhs) <= Expression.get_noise(expr, variables)

    @staticmethod
    def get_noise(expr: z3.ExprRef, variables: Dict[z3.ArithRef, float]) -> float:
        if len(expr.children()) == 0:
            if isinstance(expr, z3.ArithRef) and str(expr) in variables:
                return variables[str(expr)]
            else:
                return 0.0
        noises = []
        for c in expr.children():
            noises.append(Expression.get_noise(c, variables))
        if str(expr.decl()) == '*':
            f = 1.0
            for i in noises:
                f *= i
            return f
        elif str(expr.decl()) == '**':
            if isinstance(expr.children()[1], z3.IntNumRef):
                return math.pow(noises[0], int(expr.children()[1]))
            else:
                #TODO: FIX
                return noises[0]
        else:
            return math.fsum(noises)


class Idle(Specification):
    def __init__(self) -> None:
        super().__init__("idle",
            """
            true
            """,
            """
            (and (= _latitude __latitude)
                (= _longitude __longitude)
                (= _altitude __altitude)
                (= _armed __armed)
                (= _armable __armable)
                (= _mode __mode))
            """)

