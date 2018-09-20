__all__ = ['Specification', 'Expression', 'Idle']

from typing import List, Dict, Any, Tuple
import logging
import random
import math

import attr
import sexpdata
import z3

from .configuration import Configuration
from .state import State
from .environment import Environment

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


class InvalidExpression(Exception):
    pass


class Expression(object):
    def __init__(self, s_expression: str) -> None:
        if not Expression.is_valid(s_expression):
            raise InvalidExpression

        self.__expression = s_expression

    @property
    def expression(self) -> str:
        return self.__expression

    @staticmethod
    def is_valid(string: str) -> bool:
        try:
            parsed = sexpdata.loads(string)
        except (sexpdata.ExpectClosingBracket, sexpdata.ExpectNothing) as e:
            return False
        return True

    def is_satisfied(self,
                     command: 'Command',
                     state_before: State,
                     state_after: State,
                     environment: Environment,
                     config: Configuration
                     ) -> bool:
        logger.debug("Checking for command: %s", command.name)  # FIXME
        solver = z3.SolverFor("QF_NRA")
        smt, decls = self._prepare_query(command, state_before, state_after)
        expr = self.get_expression(decls, state_before)
        smt.extend(expr)
        logger.info("SMT: %s", smt)
        solver.add(smt)
        logger.debug("Z3 result: %s", str(solver.check()))
        return solver.check() == z3.sat

    def _prepare_query(self,
                       command: 'Command',
                       state_before: State,
                       state_after: State=None
                       ) -> Tuple[List[z3.ExprRef], Dict[str, Any]]:
        decls = self.get_declarations(command, state_before)
        smt = Expression.values_to_smt('$', command.to_json(), decls)
        smt.extend(Expression.values_to_smt('_', state_before.to_json(), decls))
        if state_after:
            smt.extend(Expression.values_to_smt('__', state_after.to_json(), decls))
        return smt, decls

    def get_declarations(self,
                         command: 'Command',
                         state: State,
                         postfix: Optional[str] = None
                         ) -> Dict[str, Any]:
        if not postfix:
            postfix = ''

        declarations = {}

        # Declare all parameters
        for p in command.parameters:
            ex = Expression._type_to_z3(p.type, '${}{}'.format(p.name, postfix))
            declarations['${}'.format(p.name)] = ex

        # Declare all state variables
        for v in state.__class__.variables:
            n = v.name
            typ = v.type
            declarations['_{}'.format(n)] = Expression._type_to_z3(type(v), '_{}{}'.format(n, postfix))
            declarations['__{}'.format(n)] = Expression._type_to_z3(type(v), '__{}{}'.format(n, postfix))
            # TODO right now we don't have a way to find out the type of state variables

        return declarations

    @staticmethod
    def _type_to_z3(typ, name: str):
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

    def get_expression(self, decls: Dict[str, Any], state: State, postfix: str="") -> List[z3.ExprRef]:
        expr = list(z3.parse_smt2_string('(assert {})'.format(self.expression), decls=decls))
        variables = {}
        for v in state.variables:
            variables['_{}{}'.format(v.name, postfix)] = float(v.noise) if v.is_noisy else 0.0
            variables['__{}{}'.format(v.name, postfix)] = float(v.noise) if v.is_noisy else 0.0
        expr_with_noise = [Expression.recreate_with_noise(e, variables) for e in expr]
        return expr_with_noise

    @staticmethod
    def recreate_with_noise(expr: z3.ExprRef, variables: Dict[z3.ArithRef, float]) -> z3.ExprRef:
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


class Specification():

    def __init__(self, name: str, precondition: str, postcondition: str) -> None:

        self.__name = name
        self.__precondition = Expression(precondition)
        self.__postcondition = Expression(postcondition)
        super().__init__()

    @property
    def precondition(self) -> Expression:
        return self.__precondition

    @property
    def postcondition(self) -> Expression:
        return self.__postcondition

    @property
    def name(self) -> str:
        return self.__name

    def timeout(self, command: 'Command', state: State, environment: Environment,
        config: Configuration) -> float:
        # TODO fix this
        return 1.0

    def get_constraint(self, command: 'Command', state: State, postfix: str='')\
                                        -> Tuple[List[z3.ExprRef], Dict[str, Any]]:
        decls = self.precondition.get_declarations(command, state, postfix)
        smt = self.precondition.get_expression(decls, state, postfix)
        smt.extend(self.postcondition.get_expression(decls, state, postfix))

        return smt, decls


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

