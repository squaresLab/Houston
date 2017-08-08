try:
    import docker
except ImportError:
    pass

import sys
import requests
import mission

class SystemContainer(object):
    """
    System proxies are used to

    - ensures clean-up
    """
    def __init__(self, iden, image, port):
        """
        Constructs a new SystemContainer

        :param  iden:   the identifier of the system to which this container\
                        belongs
        :param  image:  the name of the Docker image to use for this container
        :param  port:   the number of the port that the Houston server should\
                        run on
        """
        assert(isinstance(port, int) and not port is None)
        command = 'sudo houstonserver {}'.format(port)
        ports = {
            ('{}/tcp'.format(port)): ('127.0.0.1', port)
        }

        self.__systemIdentifier = iden
        self.__port = port
        client = docker.from_env()
        # TODO: I'm not too happy about the network_mode setting
        self.__container = client.containers.run(image,
                                                 command,
                                                 network_mode='host',
                                                 ports=ports,
                                                 detach=True)

        # TODO: enforce time-out
        # blocks until server is running
        for line in self.__container.logs(stream=True):
            line = line.strip()
            if line.startswith('* Running on http://'):
                break
                                                 

    def __del__(self):
        """
        Ensures the associated Docker container is discarded once this
        resource is no longer needed.
        """
        if not self.__container is None:
            self.destroy()


    def ready(self):
        """
        Returns true if the server running inside this system container is
        ready to accept requests.
        """
        return True


    def systemIdentifier(self):
        """
        Returns the identifier of the system to which this container belongs.
        """
        return self.__systemIdentifier


    def port(self):
        """
        Returns the port in use by this container.
        """
        return self.__port


    def container(self):
        """
        Returns a handle for the associated Docker container
        """
        return self.__container


    def execute(self, msn):
        """
        Executes a given mission inside this container and returns the result.
        """
        assert(isinstance(msn, mission.Mission))
        assert(not msn is None)
        jsn = msn.toJSON()
        url = 'http://127.0.0.1:{}/executeMission'.format(self.__port)
        print(jsn)
        r = requests.post(url, jsn)

        print(r.json())

        # TODO: add timeout
        # TODO: handle unexpected responses
        return mission.MissionOutcome.fromJSON(r.json())


    def destroy(self):
        """
        Destroys the attached Docker container.
        """
        print("Destroying container...")
        print(self.__container.logs(stdout=True, stderr=True))

        self.__container.kill()
        self.__container.remove(force=True)
        self.__container = None
