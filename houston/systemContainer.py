import docker
import requests

class SystemContainer(object):
    """
    System proxies are used to 

    - ensures clean-up
    """
    @staticmethod
    def create(iden, image, port):
        """
        Constructs a new SystemContainer

        :param  iden:   the identifier of the system to which this container\
                        belongs
        :param  image:  the name of the Docker image to use for this container
        :param  port:   the number of the port that the Houston server should\
                        run on
        """
        assert(isinstance(port, int) and not port is None)
        systemIdentifier = "ardupilot"
        image = "ardupilot" # TODO hardcoded, for now
        command = 'houstonserver {}, {}'.format(systemIdentifier, port)
        ports = {
            ('{}/tcp'.format(port)): ('127.0.0.1', port)
        }
        container = docker.containers.run(image,
                                          command,
                                          ports=ports,
                                          auto_remove=True,
                                          detach=True)
        return SystemContainer(container, port)


    def __init__(self, container, port):
        assert(isinstance(container, docker.Container))
        assert(not container is None)
        self.__container = container
        self.__port = port

    
    def __del__(self):
        """
        Ensures the associated Docker container is discarded once this
        resource is no longer needed.
        """
        if not self.__container is None:
            self.destroy()


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
        assert(isinstance(mission, mission.Mission), mission)
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
