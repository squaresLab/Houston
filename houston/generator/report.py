import copy

from houston.system import System
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

        system = System.from_json(jsn['settings']['system'])
        image = jsn['settings']['image']
        resource_usage = ResourceUsage.from_json(jsn['resources']['used'])
        resource_limits = ResourceLimits.from_json(jsn['resources']['limits'])

        return MissionGeneratorReport(system, image, history, outcomes, failed, resource_usage, resource_limits, result)


    def __init__(self, system, image, history, outcomes, failed, resource_usage, resource_limits, result):
        self.__system = system
        self.__image = image
        self.__history = history
        self.__outcomes = outcomes
        self.__failed = failed
        self.__resource_usage = resource_usage
        self.__resource_limits = resource_limits
        self.__result = result

 
    def outcome(self, mission):
        return self.__outcomes[mission]

    
    @property
    def system(self):
        return self.__system


    @property
    def image(self):
        return self.__image


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

        report = {
            'history': history,
            'failed': failed,
            'result': [m.to_json() for m in self.__result],
            'settings': {
                'system': self.system.to_json(),
                'image': self.image
            },
            'resources': {
                'used': self.resource_usage.to_json(),
                'limits': self.resource_limits.to_json()
            }
        }
        return {'report': report}
