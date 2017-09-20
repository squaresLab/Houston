import threading
import houston.manager as mgr


class MissionRunner(threading.Thread):
    def __init__(self, detector):
        super(MissionPoolWorker, self).__init__()
        self.daemon = True # mark as a daemon thread
        self.__detector = detector
        self.__container = mgr.createContainer(self.__detector.system,
                                               self.__detector.image)
        self.__reset_counter()
        

    def __reset_counter(self):
        self.__counter = 0
        self.__reset = random.randint(3, 5) # TODO: use RNG


    # TODO: debug and optimise
    def __prepare_container(self):
        if self.__counter == self.__reset:
            self.__reset_counter()
            self.__container.reset()
        self.__counter += 1


    def run(self):
        """
        Continues to process jobs.
        """
        while True:
            m = self.__pool.fetch()
            if m is None:
                return

            self.__prepare_container()
            outcome = self.__container.execute(m)
            self.__pool.report(outcome)
        

    def shutdown(self):
        print("shutting down worker: {}".format(self))
        if self.__container is not None:
            mgr.destroy_container(self.__container)
            self.__container = None


class MissionRunnerPool(object):
    def __init__(self, size):
        assert isinstance(size, int)
        assert size > 0

        self.__size = size


    @property
    def size(self):
        return self.__size
