import docker

class SystemContainer(object):
    """
    System proxies are used to 

    - ensures clean-up
    """
    @staticmethod
    def create(port):
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

    
    def container(self):
        """
        Returns a handle for the associated Docker container
        """
        return self.__container

    
    def execute(self, mission):
        """
        Executes a given mission inside this container and returns the result.
        """
        raise NotImplementedError


    def destroy(self):
        """
        Destroys the attached Docker container.
        """
        container.kill()
