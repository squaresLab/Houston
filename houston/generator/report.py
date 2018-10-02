import copy

from ..system import System
from ..test import Test, TestOutcome, TestSuite
from .resources import ResourceUsage, ResourceLimits


class TestGeneratorReport(object):
    """
    Used to provide a summary of a test generation trial.
    """
    @staticmethod
    def from_json(jsn):
        assert isinstance(jsn, dict)

        jsn = jsn['report']
        history = [Test.from_json(h['test']) for h in jsn['history']]

        outcomes = {}
        for h in jsn['history']:
            test = Test.from_json(h['test'])
            outcome = TestOutcome.from_json(h['outcome'])
            outcomes[test] = outcome

        failed = [Test.from_json(f['test']) for f in jsn['failed']]
        # TODO read coverage
        suite = TestSuite.from_json(jsn['suite'])

        system = System.from_json(jsn['settings']['system'])
        resource_usage = ResourceUsage.from_json(jsn['resources']['used'])
        resource_limits = ResourceLimits.from_json(jsn['resources']['limits'])

        return TestGeneratorReport(system,
                                      history,
                                      outcomes,
                                      failed,
                                      resource_usage,
                                      resource_limits,
                                      suite)

    def __init__(self,
                 system,
                 history,
                 outcomes,
                 failed,
                 resource_usage,
                 resource_limits,
                 coverage,  # FIXME what is this?
                 suite):
        self.__system = system
        self.__history = history
        self.__outcomes = outcomes
        self.__failed = failed
        self.__resource_usage = resource_usage
        self.__resource_limits = resource_limits
        self.__suite = suite
        self.__coverage = coverage

    def outcome(self, test):
        return self.__outcomes[test]

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
        history = []
        for m in self.__history:
            jsn = {'test': m.to_json(),
                   'outcome': self.outcomes(m).to_json()}
            history.append(jsn)

        failed = []
        for m in self.__failed:
            jsn = {'test': m.to_json(),
                   'outcome': self.outcomes(m).to_json()}
            failed.append(jsn)

        # TODO not a good way to report coverage
        coverage = []
        for (m, cov) in self.__coverage.items():
            jsn = {'test': m.to_json(),
                   'coverage': cov.to_dict()}
            coverage.append(jsn)

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
