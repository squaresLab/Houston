import random
import logging
import re
import z3
from typing import Set, Optional, Tuple, Dict, List, Any

from ..action import Action
from ..branch import BranchPath
from .root_cause import MissionDomain
from ..system import System
from ..specification import Expression
from ..state import State
from ..environment import Environment
from ..mission import Mission, MissionOutcome

logging.basicConfig(filename="symex.log",level=logging.DEBUG)
logger = logging.getLogger(__name__)
#logger.setLevel(logging.DEBUG)


class SymbolicExecution(object):

    def __init__(self, system: System, initial_state: State, environment: Environment):
        self.__system = system
        self.__initial_state = initial_state
        self.__environment = environment


    @property
    def system(self):
        return self.__system


    @property
    def initial_state(self):
        return self.__initial_state


    @property
    def environment(self):
        return self.__environment


    def execute_symbolically(self, mission: Mission) -> List[Mission]:
        """
        Having the sequense of actions in `mission` this function
        will generate parameters for those actions in order to
        explore all possible action branches.
        """

        rng = random.Random(1000)
        actions = mission.actions
        all_paths = []
        all_missions = []
        self._dfs(actions, 0, BranchPath([]), all_paths)

        for bp in all_paths:
            logger.info("BP: " + str(bp))
            solver = z3.Solver()
            smts = []
            branches = bp.branches(system=self.__system)
            seq_id = 0
            mappings = {}
            for b in branches:
                smt, decls = b.specification.get_constraint(self.initial_state, "__{}".format(seq_id))

                for pb in b.schema.branches:
                    if pb.id == b.id:
                        break
                    smt.append(z3.Not(pb.specification.precondition.get_expression(decls)[0]))

                logger.debug("BBBB {}".format(smts))
                mappings[seq_id] = decls
                smts.extend(smt)
                seq_id += 1

            smts.extend(self._connect_pre_and_post(seq_id - 1, mappings))
            logger.debug("AAA " + str(smt))
#            solver.from_string(smt)
            solver.add(smts)


            if not solver.check() == z3.sat:
                logger.info("UNSAT")
                continue

            logger.info("SAT")

            model = solver.model()
            actions = []
            seq_id = 0
            for b in branches:
                parameters = {}
                for p in b.specification.parameters:
                    try:
                        parameters[p.name] = eval(str(model[mappings[seq_id]["${}".format(p.name)]]))
                    except KeyError:
                        parameters[p.name] = p.generate(rng)
                actions.append(Action(b.schema, parameters))
                seq_id += 1

            all_missions.append(Mission(self.environment, self.initial_state, actions))

        return all_missions

    def _connect_pre_and_post(self, number: int, mappings: Dict[int, Dict[str, Any]]) -> List:
        assert(number >= 0)
        s = []
        for n, v in self.initial_state.to_json().items():
            for i in range(0, number):
                s.append(mappings[i]['__{}'.format(n)] == mappings[i+1]['_{}'.format(n)])
        s.extend(Expression.values_to_smt('_', self.initial_state.to_json(), mappings[0]))
        return s

    def _dfs(self, actions, start_index, path: BranchPath, all_paths: List[BranchPath] = []):
        if start_index == len(actions):
            all_paths.append(path)
            return
        for b in self.system.schemas[actions[start_index].schema_name].branches:
            self._dfs(actions, start_index + 1, path.extended(b), all_paths)

