class MissionGeneratorReport(object):
    """
    Used to provide a summary of a mission generation trial.
    """

    def __init__(self, history, failed, resource_usage, resource_limits, result):
        self.__history = history
        self.__failed = failed
        self.__resource_usage = resource_usage
        self.__resource_limits = resource_limits
        self.__result = result

    
    @property
    def history(self):
        return self.__history


    @property
    def resource_usage(self):
        return self.__resource_usage


    @property
    def resource_limits(self):
        return self.__resource_limits


    @property
    def result(self):
        return self.__result


    def to_json(self):
        return {'report': {
            'history': self.history,
            'failed': self.failed,
            'result': {
                self.result
            },
            'resources': {
                'used': self.resource_usage.to_json(),
                'limits': self.resource_limits.to_json()
            }
        }}
