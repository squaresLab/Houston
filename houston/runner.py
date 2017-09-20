import threading
import houston.manager as mgr


class MissionRunner(threading.Thread):
    def __init__(self, pool):
        assert isinstance(pool, MissionRunnerPool)
        super(MissionPoolWorker, self).__init__()
        self.daemon = True # mark as a daemon thread

        self.__pool = pool
        self.__container = mgr.createContainer(pool.system, pool.image)
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
        # print("shutting down worker: {}".format(self))
        if self.__container is not None:
            mgr.destroy_container(self.__container)
            self.__container = None


class MissionRunnerPool(object):
    def __init__(self, size, source):
        assert isinstance(size, int)
        assert size > 0

        # if a list is provided, use an iterator for that list
        if isinstance(source, list):
            source = source.__iter__()

        self.__size = size
        self.__source = source
        self.__runners = []
        self._lock = threading.Lock()


    @property
    def size(self):
        """
        The number of runners used by the pool.
        """
        return self.__size


    def fetch(self):
        """
        Returns the next mission from the (lazily-generated) queue, or None if
        there are no missions left to run.
        """
        # acquire fetch lock
        self._lock.acquire()
        try:
            return self.__source.next()

        except StopIteration:
            return None

        finally:
            self._lock.release()
