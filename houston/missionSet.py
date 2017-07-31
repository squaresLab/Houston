class MissionSet(object):


    def __init__(self):
        self.__contents = set()

    def toFile(self, fn):
        """
        Writes the contents of this mission set to a given file, in a JSON
        format.

        :param  fn  The path of the file to which the test set shuld be written.
        """

