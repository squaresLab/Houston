from houston.generator.base import MissionGenerator
from houston.mission import Mission


class MutationBasedMissionGenerator(MissionGenerator):
    def __init__(self,
                 system,
                 initial_state,
                 env,
                 threads = 1,
                 action_generators = [],
                 max_num_actions = 10,
                 initial_mission = None):
        super(MutationBasedMissionGenerator, self).__init__(system, threads, action_generators, max_num_actions)
        self.__initial_state = initial_state
        self.__env = env
        self.__initial_mission = initial_mission if initial_mission else self._generate_random_mission()
        self.__in_progress_missions = {}
        self.__most_fit_missions = [] #TODO this can be a dictionary instead of a list

    
    @property
    def initial_state(self):
        """
        The initial state used by all missions produced by this generator.
        """
        return self.__initial_state


    @property
    def initial_mission(self):
        """
        Returns the initial mission to start the mutation from.
        """
        return self.__initial_mission


    @property
    def env(self):
        """
        The environment used by all missions produced by this generator.
        """
        return self.__env


    @property
    def most_fit_missions(self):
        """
        Return the most fit missions generated.
        """
        return self.__most_fit_missions


    def _generate_action(self, schema):
        generator = self.action_generator(schema)
        if generator is None:
            return schema.generate(self.rng)
        return generator.generate_action_without_state(self.system, self.__env, self.rng)


    def _generate_random_mission(self):
        schemas = list(self.system.schemas.values())
        actions = []
        for _ in range(self.rng.randint(1, self.max_num_actions)):
            schema = self.rng.choice(schemas)
            actions.append(self._generate_action(schema))
        return Mission(self.__env, self.__initial_state, actions)


    def _get_fitness(self, mission):
        #TODO Get the fitness of this mission
        if mission == self.__initial_mission:
            return 1.0

        outcome = self.outcomes[mission]
        coverage = self.coverage[mission]
        initial_coverage = self.coverage[self.__initial_mission]

        fitness = 1.0

        if not outcome.passed:
            fitness *= 5.0

        similar_coverage = coverage.intersection(initial_coverage)
        fitness += len(similar_coverage)

        return fitness


    def _add_action_operator(self, mission):
        actions = mission.actions
        if len(actions) >= self.max_num_actions:
            return None
        schema = self.rng.choice(list(self.system.schemas.values()))
        actions.insert(self.rng.randint(0, len(actions)-1), self._generate_action(schema))
        return Mission(self.__env, self.__initial_state, actions)


    def _delete_action_operator(self, mission):
        actions = mission.actions
        if len(actions) <= 1:
            return None
        actions.pop(self.rng.randint(0, len(actions)-1))
        return Mission(self.__env, self.__initial_state, actions)


    def _edit_action_operator(self, mission):
        #TODO implement editing an existing action
        return None


    def _mutate_mission(self, mission):
        mutation_operators = [self._add_action_operator, self._delete_action_operator,
                              self._edit_action_operator]
        generated_mission = None
        while not generated_mission:
            operator = self.rng.choice(mutation_operators)
            print("Operator: {}".format(str(operator)))
            generated_mission = operator(mission)
        return generated_mission


    def generate_mission(self):
        if not self.__most_fit_missions:
            self.__in_progress_missions[self.__initial_mission] = {'parent': None}
            return self.__initial_mission

        parent = self.rng.choice(self.__most_fit_missions)
        mission = self._mutate_mission(parent)
        self.__in_progress_missions[mission] = {'parent': parent}
        print("Mutated: {}\nfrom: {}".format(mission.to_json(), parent.to_json()))
        return mission


    def record_outcome(self, mission, outcome, coverage):
        """
        Records the outcome of a given mission. The mission is logged to the
        history, and its outcome is stored in the outcome dictionary. If the
        mission failed, the mission is also added to the set of failed
        missions.
        """
        self.history.append(mission)
        self.outcomes[mission] = outcome
        self.coverage[mission] = coverage


        if outcome.failed:
            self.failures.add(mission)

        if not mission in self.__in_progress_missions:
            print("Something went wrong! mission is not in progress")

        fitness = self._get_fitness(mission)
        parent = self.__in_progress_missions[mission]['parent']
        if not parent:
            # initial mission
            self.most_fit_missions.append(mission)
            self.__in_progress_missions.pop(mission)
            return

        parent_fitness = self._get_fitness(parent)
        if fitness >= parent_fitness:
            if len(self.most_fit_missions) == self.resource_limits.num_missions_selected:
                self.most_fit_missions.remove(parent)
            self.most_fit_missions.append(mission)
        self.__in_progress_missions.pop(mission)



