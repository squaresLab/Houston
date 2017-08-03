import random
import system
import mission

"""
A registry of systems known to Houston, indexed by their identifiers.
"""
__systems = {}

"""
The pool of ports that are open and available to be used.
"""
__port_pool = set(i for i in range(500, 1000))

"""
The set of containers that are actively in use.
"""
__containers = set()


def registerSystem(systm):
    """
    Registers a system with Houston.

    @TODO   we could perform this automatically using magic methods / class hooks
    """
    global __systems
    assert (isinstance(systm, system.System) and not systm is None)
    iden = systm.identifier()
    if iden in __systems:
        raise Error("system already registered with name: {}".format(iden))
    __systems[iden] = systm


def getSystem(identifier):
    """
    Returns the system associated with a given identifier.
    """
    assert (isinstance(identifier, str))
    return __systems[identifier]


def createContainer(systm, image):
    """
    Constructs a fresh, ephemeral container for a given system using a
    specified Docker image.
    
    :param  systm:  the System object
    :param  image:  the name of the Docker image that should be used to spawn\
                    the container

    :returns    A new SystemContainer for the given system
    """
    global __port_pool
    global __containers

    assert (isinstance(systm, systm.System))
    assert (not system is None)

    iden = systm.identifier()
    assert (iden in __systems)

    # TODO: ensure the port is returned to the pool once we're done with the
    #       container
    port = random.choice(__port_pool)
    __port_pool.remove(port)

    container = system.SystemContainer(iden, image, port)
    __containers.add(container)

    return container
