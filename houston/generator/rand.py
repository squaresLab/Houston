from houston.generator.base import MissionGenerator
from houston.mission import Mission


class RandomMissionGenerator(MissionGenerator):
    def __init__(self):
        pass


    def generate_mission(self):
        schemas = self.system.schemas.values()
        actions = []
        for _ in range(self.rng.randint(1, self.max_num_actions)):
            schema = self.rng.choice(schemas)
            actions.append(self.generate_action(schema))

        return Mission(self.__env, self.__initial_state, actions)
