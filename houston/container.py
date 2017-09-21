import os
import houston
import site
import sys
import requests
import mission
import timeit
import threading
import random

from system import System
from util import printflush


# Find the location of Houston on disk
# PATH_TO_SITE_PKGS = site.getsitepackages()[0]
PATH_TO_HOUSTON_EGG = os.path.dirname(os.path.dirname(houston.__file__))
HOUSTON_SCRIPT_PATHS = [ # TODO: use `which` command
    '/usr/local/bin/houstonserver'
]
MAX_NUM_ATTEMPTS = 3


class Container(object):
    """


    Attributes:

        _lock:          Used to guard the port and container pools.
        _port_pool:     The set of ports that are open and available to be
            used by provisioned containers.
        _running:       The set of containers that have been provisioned
            and that are currently in use.
    """
    _manager_lock = threading.Lock()
    _port_pool = set(i for i in range(10000, 10500))
    _running = set()


    @staticmethod
    def provision(system, image, verbose=False):
        """
        Constructs a fresh, ephemeral container for a given system using a
        specified Docker image.

        :param  systm:  the System object
        :param  image:  the name of the Docker image that should be used to spawn\
                        the container
        :param  verbose:    a flag indicating whether the outputs of the container \
                            should be printed to the stdout upon its destruction

        :returns    A new Container for the given system
        """
        assert isinstance(system, System)

        Container._manager_lock.acquire()
        try:
            port = random.sample(Container._port_pool, 1)[0]
            Container._port_pool.remove(port)
            container = Container(system, image, port, verbose=verbose)
            Container._running.add(container)
            return container
        finally:
            Container._manager_lock.release()


    @staticmethod
    def set_port_range(start, end):
        """
        Updates the set of ports that are available to Houston. This should not
        be called whilst containers are being provisioned, or missions are being
        executed.
        """
        assert isinstance(start, int)
        assert (start >= 1024 and start < 65535)
        assert isinstance(end, int)
        assert (end >= 1024 and end < 65535)
        assert (start < end)  

        Container._manager_lock.acquire()
        try:
            Container._port_pool = set(i for i in range(start, end))
        finally:
            Container._manager_lock.release()


    def __init__(self, system, image, port, verbose=False):
        """
        Constructs a new container

        :param  system:     the system under test
        :param  image:      the name of the Docker image to use for this container
        :param  port:       the number of the port that the Houston server should\
                            run on
        :param  verbose:    a flag indicating whether the output from this \
                            container should be dumped before its destruction.
        """
        assert (isinstance(system, System))
        assert (isinstance(port, int))
        assert (isinstance(verbose, bool))
        assert (isinstance(image, str) or isinstance(image, unicode))
        assert (image != "")
        assert (port >= 1024 and port < 65535)

        self.__verbose = verbose
        self.__system = system
        self.__port = port
        self.__image = image
        self.__container = None
        self.__prepare()


    def __prepare(self):
        import docker
        if self.__container is not None and self.__verbose:
            printflush(self.__container.logs(stdout=True, stderr=True))

        print("preparing container: {}".format(self))
        command = 'houstonserver {}'.format(self.__port)
        ports = {self.__port: self.__port}

        # prepare Houston library and scripts for auto-mounting
        volumes = {
            PATH_TO_HOUSTON_EGG: {'bind': PATH_TO_HOUSTON_EGG, 'mode': 'ro'}
        }
        for path in HOUSTON_SCRIPT_PATHS:
            volumes[path] = {'bind': path, 'mode': 'ro'}

        client = docker.from_env()
        self.__container = client.containers.run(self.__image,
                                                 command,
                                                 network_mode='bridge',
                                                 ports=ports,
                                                 volumes=volumes,
                                                 detach=True)

        # blocks until server is running
        for line in self.__container.logs(stream=True):
            line = line.strip()
            if line.startswith('* Running on http://'):
                break


    def reset(self):
        self.destroy()
        self.__prepare()


    def ready(self):
        """
        Returns true if the server running inside this system container is
        ready to accept requests.
        """
        return True


    @property
    def port(self):
        """
        The port used by the Houston server on this container.
        """
        return self.__port


    def execute(self, msn):
        """
        Executes a given mission inside this container and returns the result.
        """
        assert(isinstance(msn, mission.Mission))

        jsn = {'system': self.__system.to_json(),
               'mission': msn.to_json()}
        url = 'http://127.0.0.1:{}/executeMission'.format(self.__port)
        start_time = timeit.default_timer()

        for attempts in range(MAX_NUM_ATTEMPTS):
            try:
                r = requests.post(url, json=jsn)
                outcome = mission.MissionOutcome.from_json(r.json())
                #if self.__verbose:
                #    print(outcome.toJSON())
                return outcome
            except ValueError:
                printflush("server error: {}".format(self.__container.logs()))
                printflush("mission attempt failed: resetting container")
                self.reset()
            except:
                printflush("Unexpected server error: {}".format(self.__container.logs()))
                raise

        total_time = timeit.default_timer() - start_time
        return mission.CrashedMissionOutcome(total_time)


    def destroy(self):
        """
        Destroys the attached Docker container.
        """
        if self.__verbose:
            printflush(self.__container.logs(stdout=True, stderr=True))

        if self.__container is not None:
            self.__container.remove(force=True)
            self.__container = None

        # release the port and remove this container from the set of running
        # containers
        Container._manager_lock.acquire()
        try:
            Container._port_pool.add(self.__port)
            Container._running.remove(self)
        finally:
            Container._manager_lock.release()
