import copy

from houston.system import System
from houston.mission import Mission, MissionOutcome, MissionSuite
from houston.generator.resources import ResourceUsage, ResourceLimits


class MissionGeneratorReport(object):
    """
    Used to provide a summary of a mission generation trial.
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)

        jsn = jsn['report']
        history = [Mission.from_json(h['mission']) for h in jsn['history']]
        outcomes = \
            {Mission.from_json(h['mission']): MissionOutcome.from_json(h['outcome']) for h in jsn['history']}
        failed = [Mission.from_json(f['mission']) for f in jsn['failed']]
        # TODO read coverage
        suite = MissionSuite.from_json(jsn['suite'])

        system = System.from_json(jsn['settings']['system'])
        resource_usage = ResourceUsage.from_json(jsn['resources']['used'])
        resource_limits = ResourceLimits.from_json(jsn['resources']['limits'])

        return MissionGeneratorReport(system, history, outcomes, failed, resource_usage, resource_limits, suite)


    def __init__(self, system, history, outcomes, failed, resource_usage, resource_limits, coverage, suite):
        self.__system = system
        self.__history = history
        self.__outcomes = outcomes
        self.__failed = failed
        self.__resource_usage = resource_usage
        self.__resource_limits = resource_limits
        self.__suite = suite
        self.__coverage = coverage

 
    def outcome(self, mission):
        return self.__outcomes[mission]

    
    @property
    def system(self):
        return self.__system


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
    def suite(self):
        return self.__suite


    def to_json(self):
        history = [(m.to_json(), self.outcome(m).to_json()) for m in self.__history]
        history = [{'mission': m, 'outcome': o} for (m, o) in history]

        failed = [(m.to_json(), self.outcome(m).to_json()) for m in self.__failed]
        failed = [{'mission': m, 'outcome': o} for (m, o) in failed]

        # TODO not a good way to report coverage
        coverage = [(m.to_json(), self.__coverage[m].to_dict()) for m in self.__coverage]
        coverage = [{'mission': m, 'coverage': c} for (m, c) in coverage]

        report = {
            'history': history,
            'failed': failed,
            'coverage': coverage,
            'suite': self.suite.to_json(),
            'settings': {
                'system': self.system.to_json()
            },
            'resources': {
                'used': self.resource_usage.to_json(),
                'limits': self.resource_limits.to_json()
            }
        }
        return {'report': report}
