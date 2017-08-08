import docker
import requests

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
        command = 'houstonserver {}, {}'.format(iden, port)
        client = docker.from_env()
        ports = {
            ('{}/tcp'.format(port)): ('127.0.0.1', port)
        }
        self.__systemIdentifier = iden
        self.__port = port
        self.__container = client.containers.run(image,
                                                 command,
                                                 ports=ports,
                                                 detach=True)


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
        return DOCKER_CHECK(server.READY_FILE)


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


    def execute(self, mission):
        """
        Executes a given mission inside this container and returns the result.
        """
        assert(isinstance(mission, mission.Mission))
        assert(not mission is None)
        jsn = mission.toJSON()
        url = 'http://127.0.0.1:{}/executeMission'.format(port)
        r = requests.post(url, jsn)

        # TODO: add timeout
        # TODO: handle unexpected responses
        return mission.MissionOutcome.fromJSON(r.json())


    def destroy(self):
        """
        Destroys the attached Docker container.
        """
        self.__container.kill()
