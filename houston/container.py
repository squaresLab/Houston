import os
import site
import sys
import requests
import time
import timeit
import threading
import random
import houston
import houston.mission

from houston.system import System
from houston.util import printflush


# Find the location of Houston on disk
# PATH_TO_SITE_PKGS = site.getsitepackages()[0]
#
# TODO: solve the issue of running `houstonserver` on the container. The best
#   way to tackle this issue is to use a volume to share the source code with
#   the container, and to install it from there. In general, mounting eggs
#   won't work, as the host and container versions of Python are not
#   guaranteed to be the same.
#
#
print(PATH_TO_HOUSTON_EGG)
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
    def provision(system, artefact, verbose=False):
        """
        Constructs a fresh, ephemeral container for a given system using a
        specified RepairBox artefact.

        :returns    A new Container for the given system
        """
        import repairbox

        assert isinstance(system, System)
        assert isinstance(artefact, repairbox.Artefact)
        assert isinstance(verbose, bool)

        Container._manager_lock.acquire()
        try:
            port = random.sample(Container._port_pool, 1)[0]
            Container._port_pool.remove(port)
            rbx = Container(system, artefact, port, verbose=verbose)
            Container._running.add(rbx)
            return rbx
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


    def __init__(self, system, artefact, port, verbose=False):
        """
        Constructs a new container
        """
        import repairbox

        assert isinstance(system, System)
        assert isinstance(artefact, repairbox.Artefact)
        assert isinstance(port, int)
        assert isinstance(verbose, bool)
        assert (port >= 1024 and port < 65535)

        self.__verbose = verbose
        self.__system = system
        self.__port = port
        self.__artefact = artefact
        self.__rbx = None
        self.__daemon = None
        self.__prepare()


    def __prepare(self):
        command = '/usr/local/bin/houstonserver {}'.format(self.__port)
        ports = {self.__port: self.__port}
        volumes = {
            PATH_TO_HOUSTON_EGG: {'bind': PATH_TO_HOUSTON_EGG, 'mode': 'ro'}
        }
        for path in HOUSTON_SCRIPT_PATHS:
            volumes[path] = {'bind': path, 'mode': 'ro'}

        # provision a container via RepairBox
        self.__rbx = self.__artefact.provision(volumes=volumes,
                                               network_mode='bridge',
                                               ports=ports)
        self.__daemon = self.__rbx.execute_command(command, stdout=True, stderr=True, block=False)

        # blocks until server is running
        for line in self.__daemon.output:
             line = line.strip().decode('utf8')
             print(line)
             if line.startswith('* Running on http://'):
                 break

        # what if the daemon failed?
        assert self.__daemon.running


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

    
    def inspect(self):
        if not self.__daemon:
            return ''
        return '\n'.join(self.__daemon.output)


    def execute(self, msn):
        """
        Executes a given mission inside this container and returns the result.
        """
        from houston.mission import Mission, MissionOutcome, CrashedMissionOutcome

        assert isinstance(msn, Mission)

        jsn = {'system': self.__system.to_json(),
               'mission': msn.to_json()}
        url = 'http://127.0.0.1:{}/executeMission'.format(self.__port)
        start_time = timeit.default_timer()

        for attempts in range(MAX_NUM_ATTEMPTS):
            try:
                r = requests.post(url, json=jsn)
                outcome = MissionOutcome.from_json(r.json())
                #if self.__verbose:
                #    print(outcome.toJSON())
                return outcome
            except ValueError:
                printflush("server error: {}".format(self.inspect()))
                printflush("mission attempt failed: resetting container")
                self.reset()
            except:
                printflush("Unexpected server error: {}".format(self.inspect()))
                raise

        total_time = timeit.default_timer() - start_time
        return CrashedMissionOutcome(total_time)


    def destroy(self, reset=False):
        """
        Destroys the attached Docker container.
        """
        if self.__verbose:
            printflush(self.inspect())
        self.__daemon = None

        if self.__rbx is not None:
            self.__rbx.destroy()
            self.__rbx = None

        # release the port and remove this container from the set of running
        # containers
        Container._manager_lock.acquire()
        try:
            if not reset:
                Container._port_pool.add(self.__port)
            Container._running.remove(self)
        finally:
            Container._manager_lock.release()
