import random
import logging
import re
import z3
import copy
from typing import Set, Optional, Tuple, Dict, List, Any

from .root_cause import MissionDomain
from ..system import System
from ..specification import Specification, Expression
from ..state import State
from ..environment import Environment
from ..mission import Mission, MissionOutcome
from ..configuration import Configuration
from ..command import Command

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)


class SymbolicExecution(object):

    def __init__(self, system: System, initial_state: State, environment: Environment, configuration: Configuration):
        self.__system = system
        self.__initial_state = initial_state
        self.__environment = environment
        self.__configuration = configuration


    @property
    def system(self):
        return self.__system


    @property
    def initial_state(self):
        return self.__initial_state


    @property
    def environment(self):
        return self.__environment

    @property
    def configuration(self):
        return self.__configuration

    def execute_symbolically(self, mission: Mission) -> List[Mission]:
        """
        Having the sequense of actions in `mission` this function
        will generate parameters for those actions in order to
        explore all possible action branches.
        """

        rng = random.Random(1000)
        commands = mission.commands
        all_paths = [] # type List[List[Specification]]
        all_missions = []
        self._dfs(commands, 0, [], all_paths)

        for bp in all_paths:
            logger.info("BP: " + str(bp))
            logger.info("CMD: " + str(commands))
            solver = z3.Solver()
            smts = []
            seq_id = 0
            mappings = {}
            for b in bp:
                smt, decls = b.get_constraint(commands[seq_id], self.initial_state, "__{}".format(seq_id))

                for pb in commands[seq_id].specifications:
                    if pb.name == b.name:
                        break
                    smt.append(z3.Not(pb.precondition.get_expression(
                        decls, self.initial_state,
                        "__{}".format(seq_id))[0]))

                logger.debug("SSS {}".format(smt))
                mappings[seq_id] = decls
                smts.extend(smt)
                seq_id += 1

            smts.extend(self._connect_pre_and_post(seq_id - 1, mappings))
            logger.debug("Final " + str(smts))
#            solver.from_string(smt)
            solver.add(smts)


            if not solver.check() == z3.sat:
                logger.info("UNSAT")
                continue

            logger.info("SAT")

            model = solver.model()
            logger.debug("Model: {}".format(model))
            commands_list = []
            seq_id = 0
            for b in bp:
                parameters = {}
                for p in commands[seq_id].parameters:
                    parameters[p.name] = eval(str(model[mappings[seq_id]["${}".format(p.name)]]))
                    if parameters[p.name] == None:
                        v = p.generate(rng)
                        logger.debug("PP {} {}".format(p.name, v))
                        parameters[p.name] = v
                logger.debug("Parameters: {}".format(parameters))
                commands_list.append(commands[seq_id].__class__(**parameters))
                seq_id += 1

            logger.debug("Added: {}".format(commands_list))
            all_missions.append(Mission(self.configuration, self.environment, self.initial_state, commands_list))

        return all_missions

    def _connect_pre_and_post(self, number: int, mappings: Dict[int, Dict[str, Any]]) -> List:
        assert(number >= 0)
        s = []
        for n, v in self.initial_state.to_json().items():
            for i in range(0, number):
                s.append(mappings[i]['__{}'.format(n)] == mappings[i+1]['_{}'.format(n)])
        s.extend(Expression.values_to_smt('_', self.initial_state.to_json(), mappings[0]))
        return s

    def _dfs(self, commands: List[Command], start_index: int, path: List[Specification], all_paths: List[List[Specification]] = []):
        if start_index == len(commands):
            all_paths.append(path)
            return
        for s in commands[start_index].specifications:
            new_path = copy.deepcopy(path)
            new_path.append(s)
            self._dfs(commands, start_index + 1, new_path, all_paths)

