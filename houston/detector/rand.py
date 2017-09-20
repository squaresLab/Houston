from houston.detector.base import BugDetector, BugDetectorSummary
from houston.mission import Mission


class RandomBugDetectorSummary(BugDetectorSummary):
    """
    Used to provide a summary of a test generation trial that used the
    tree-based test generation strategy.
    """
    @staticmethod
    def from_json(jsn):
        base = BugDetectorSummary.from_json(jsn)
        return RandomBugDetectorSummary(base)


    def __init__(self, base):
        assert isinstance(base, BugDetectorSummary)
        super(RandomBugDetectorSummary, self).__init__(base.system,
                                                       base.image,
                                                       base.history,
                                                       base.outcomes,
                                                       base.failures,
                                                       base.resource_usage,
                                                       base.resource_limits)


    def toJSON(self):
        jsn = super(RandomBugDetectorSummary, self).to_json()
        jsn['summary']['settings']['algorithm'] = 'random'
        return jsn


class RandomBugDetector(BugDetector):
    def __init__(self, initial_state, env, threads = 1, action_generators = [], max_num_actions = 10):
        super(RandomBugDetector, self).__init__(threads, action_generators, max_num_actions)
        self.__initial_state = initial_state
        self.__env = env


    def summarise(self):
        summary = super(RandomBugDetector, self).summarise()
        summary = RandomBugDetectorSummary(summary)
        return summary


    def generate_action(self, schema):
       generator = self.get_generator(schema)
       if generator is None:
           return schema.generate(self._rng)
       return generator.generate_action_without_state(self.__env, self._rng)


    def generate_mission(self):
        systm = self.system
        schemas = systm.schemas.values()

        actions = []
        for _ in range(self._rng.randint(1, self.max_num_actions)):
            schema = self._rng.choice(schemas)
            actions.append(self.generate_action(schema))

        return Mission(self.__env, self.__initial_state, actions)
