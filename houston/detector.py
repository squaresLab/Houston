import copy


class ResourceLimit(object):
    """
    A convenience class used to impose limits on the bug detection process.
    """
    def __init__(self):
        pass


class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self):
        pass

    
    def detect(self, systm, image, resourceLimits):
        """

        :param      systm: the system under test
        :param      image: the name of the Dockerfile that should be used to \
                        containerise the system under test
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
        resources = {
            'used': self.__resourceUsage.toJSON(),
            'limits': self.__resourceLimits.toJSON()
        }
        summary = {
            'resources': resources
        }
        return {'summary': summary}


class IncrementalBugDetector(BugDetector):
    pass


class RandomBugDetector(BugDetector):
    pass


class RandomDirectedBugDetector(BugDetector):
    


