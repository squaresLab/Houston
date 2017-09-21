import copy

from houston.generator.resource import ResourceUsage, ResourceLimits


class MissionGeneratorReport(object):
    """
    Used to provide a summary of a mission generation trial.
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)

        jsn = jsn['report']
        history = [h['mission'] for h in jsn['history']]
        outcomes = {h['mission']: h['outcome'] for h in jsn['history']}
        failed = [f['mission'] for f in jsn['failed']]
        result = [Mission.from_json(m) for m in jsn['result']]

        resource_usage = ResourceUsage.from_json(jsn['resources']['used'])
        resource_limits = ResourceLimits.from_json(jsn['resources']['limits'])

        return MissionGeneratorReport(history, outcomes, failed, resource_usage, resource_limits, result)


    def __init__(self, history, outcomes, failed, resource_usage, resource_limits, result):
        self.__history = history
        self.__outcomes = outcomes
        self.__failed = failed
        self.__resource_usage = resource_usage
        self.__resource_limits = resource_limits
        self.__result = result

 
    def outcome(self, mission):
        return self.__outcomes[mission]


    @property
    def outcomes(self):
        return copy.copy(self.__outcomes)

    
    @property
    def history(self):
        return self.__history[:]


    @property
    def resource_usage(self):
        return self.__resource_usage


    @property
    def resource_limits(self):
        return self.__resource_limits


    @property
    def result(self):
        return self.__result[:]


    def to_json(self):
        history = [(m, self.outcome(m)) for m in self.__history]
        history = [{'mission': m, 'outcome': o} for (m, o) in history]

        failed = [(m, self.outcome(m)) for m in self.__failed]
        failed = [{'mission': m, 'outcome': o} for (m, o) in failed]

        return {'report': {
            'history': history,
            'failed': failed,
            'result': [m.to_json() for m in self.__result],
            'resources': {
                'used': self.resource_usage.to_json(),
                'limits': self.resource_limits.to_json()
            }
        }}
