import copy

class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self):
        pass

    
    def detect(self, systm, resourceLimits):
        """

        :param      systm:          the system under test
        :param      resourceLimits: a description of the resources available \
                        to the detection process, given as a ResourceLimits \
                        object

        :returns    a summary of the detection process in the form of a \
                    BugDetectionSummary object
        """
        resourceUsage = ResourceUsage()


        summary = BugDetectionSummary(resourceUsage, resourceLimits)
        return summary


class BugDetectionSummary(object):
    def __init__(self, resourceUsage, resourceLimits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
        self.__resourceUsage = copy.copy(resourceUsage)
        self.__resourceLimits = resourceLimits


    def toJSON(self):
        """
        Transforms this bug detection summary into a JSON format.
        """
        pass


class IncrementalBugDetector(BugDetector):
    pass


class RandomBugDetector(BugDetector):
    pass


class RandomDirectedBugDetector(BugDetector):
    pass
