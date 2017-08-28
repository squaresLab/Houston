from base import BugDetector, BugDetectorSummary
from mission import Mission


class RandomBugDetectorSummary(BugDetectorSummary):
    """
    Used to provide a summary of a test generation trial that used the
    tree-based test generation strategy.
    """
    @staticmethod
    def fromJSON(jsn):
        base = BugDetectorSummary.fromJSON(jsn)
        return RandomBugDetectorSummary(base)


    def __init__(self, base):
        assert (isinstance(base, BugDetectorSummary) and base is not None)
        super(RandomBugDetectorSummary, self).__init__(base.getSystem(),
                                                       base.getImage(),
                                                       base.getHistory(),
                                                       base.getOutcomes(),
                                                       base.getFailures(),
                                                       base.getResourceUsage(),
                                                       base.getResourceLimits())


    def toJSON(self):
        jsn = super(RandomBugDetectorSummary, self).toJSON()
        jsn['summary']['settings']['algorithm'] = 'random'
        return jsn


class RandomBugDetector(BugDetector):
    def __init__(self, initialState, env, threads = 1, actionGenerators = [], maxNumActions = 10):
        super(RandomBugDetector, self).__init__(threads, actionGenerators, maxNumActions)
        self.__initialState = initialState
        self.__env = env


    def summarise(self):
        summary = super(RandomBugDetector, self).summarise()
        summary = RandomBugDetectorSummary(summary)
        return summary


    def generateAction(self, schema):
       generator = self.getGenerator(schema)
       if generator is None:
           return schema.generate(self._rng)
       return generator.generateActionWithoutState(self.__env, self._rng)


    def generateMission(self):
        systm = self.getSystem()
        schemas = systm.getActionSchemas().values()
        maxNumActions = self.getMaxNumActions()
        env = self.__env
        initialState = self.__initialState

        actions = []
        for _ in range(self._rng.randint(1, maxNumActions)):
            schema = self._rng.choice(schemas)
            actions.append(self.generateAction(schema))

        return Mission(env, initialState, actions)
