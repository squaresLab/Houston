import docker

class SystemContainer(object):
    """
    System proxies are used to 
    
    - attached to a container
    - ensure container is destroyed
    """

    def __init__(self):
        pass

    def destroy(self):
        """
        Destroys the attached Docker container.
        """
