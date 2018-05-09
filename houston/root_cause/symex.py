from z3 import *
from typing import Set, Optional, Tuple, Dict, List

from houston.root_cause import MissionDomain
from houston.system import System
from houston.state import State, Environment
from houston.mission import Mission, MissionOutcome


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

        actions = mission.actions
        all_paths = []
        all_missions = []
        self_dfs(actions, 0, BranchPath([]), all_paths)

        for bp in all_paths:
            solver = Solver()
            branches = bp.branches
            seq_id = 0
            mappings = {}
            for b in branches:
                mapping = b.add_constraints(solver, seq_id)
                mappings[b] = mapping
                seq_id += 1

            if not solver.check() == sat:
                continue

            model = solver.model()
            actions = []
            for b in branches:
                mapping = mappings[b]
                parameters = {}
                for z3_var, param in mapping:
                    parameters[param] = model[z3_var]
                actions.append(Action(b.schema, parameters))

            all_missions.append(Mission(self.environment, self.initial_state, actions))

        return all_missions


    def _dfs(self, actions, start_index, path: BranchPath, all_paths: List[BranchPath] = []):
        if start_index == len(actions)-1:
            all_paths.append(path)
            return
        for b in self.system.schemas[actions[start_index].schema_name].branches:
            self._dfs(actions, start_index + 1, path.extended(b), allPaths)

