from houston.generator.base import MissionGenerator
from houston.mission import Mission


class RandomMissionGenerator(MissionGenerator):
    def __init__(system, image, initial_state, env, threads = 1, action_generators = [],  max_num_actions = 10):
        self.__initial_state = initial_state
        self.__env = env

    
    @property
    def initial_state(self):
        return self.__initial_state
    

    @property
    def env(self):
        return self.__env


    def generate_action(self, schema):
       generator = self.generator(schema)
       if generator is None:
           return schema.generate(self.rng)
       return generator.generate_action_without_state(self.__env, self.rng)


    def generate_mission(self):
        schemas = self.system.schemas.values()
        actions = []
        for _ in range(self.rng.randint(1, self.max_num_actions)):
            schema = self.rng.choice(schemas)
            actions.append(self.generate_action(schema))

        return Mission(self.__env, self.__initial_state, actions)
