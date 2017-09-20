class MissionGenerator(object):

    def __init__(self, threads, max_num_actions):
        assert isinstance(threads, int)
        assert isinstance(max_num_actions, int)
        assert threads > 0
        assert max_num_actions > 0

        self.__threads = threads
        self.__max_num_actions = max_num_actions


    @property
    def threads(self):
        """
        The number of threads available to this generator.
        """
        return self.__threads


    def generate(self, system):
        pass
