from .base import MissionGenerator
from ..mission import Mission


class RandomMissionGenerator(MissionGenerator):
    def __init__(self,
                 system,
                 initial_state,
                 env,
                 threads=1,
                 action_generators=None,
                 max_num_actions=10
                 ) -> None:
        super(RandomMissionGenerator, self).__init__(system,
                                                     threads,
                                                     action_generators,
                                                     max_num_actions)
        self.__initial_state = initial_state
        self.__env = env

    @property
    def initial_state(self):
        """
        The initial state used by all missions produced by this generator.
        """
        return self.__initial_state

    @property
    def env(self):
        """
        The environment used by all missions produced by this generator.
        """
        return self.__env

    def generate_action(self, schema):
        generator = self.action_generator(schema)
        if generator is None:
            return schema.generate(self.rng)
        g = generator.generate_action_without_state
        return g(self.system, self.__env, self.rng)

    def generate_mission(self):
        schemas = list(self.system.schemas.values())
        actions = []
        for _ in range(self.rng.randint(1, self.max_num_actions)):
            schema = self.rng.choice(schemas)
            actions.append(self.generate_action(schema))
        return Mission(self.__env, self.__initial_state, actions)
