import random
import system
import mission
import systemContainer
import threading

"""
A lock is required to mutate the set of containers/ports
"""
__manager_lock = threading.Lock()

"""
A registry of system classes known to Houston, indexed by their identifiers.
"""
__systemClasses = {}

"""
The pool of ports that are open and available to be used.
"""
__port_pool = set(i for i in range(10000, 10500))

"""
The set of containers that are actively in use.
"""
__containers = set()


def registerSystemClass(name, cls):
    """
    Registers a system class with Houston.

    @TODO   we could perform this automatically using magic methods / class hooks
    """
    global __systemClasses
    if name in __systemClasses:
        raise Error("system class already registered with name: {}".format(name))
    __systemClasses[name] = cls


def setPortRange(start, end):
    """
    Updates the set of ports that are available to Houston. This should not
    be called whilst containers are being provisioned, or missions are being
    executed.
    """
    global __port_pool
    global __manager_lock

    assert (isinstance(start, int) and start is not None)
    assert (start >= 1024 and start < 65535)
    assert (isinstance(end, int) and end is not None)
    assert (end >= 1024 and end < 65535)
    assert (start < end)  

    __manager_lock.acquire()
    __port_pool = set(i for i in range(start, end))
    __manager_lock.release()


def getClassNameOfSystem(systm):
    """
    Returns the name of the system class for a given system.
    """
    assert (isinstance(systm, system.System))
    cls = type(systm)
    return getNameOfSystemClass(cls)


def getNameOfSystemClass(cls):
    """
    Returns the name associated with a given system class.
    """
    for (n, kls) in __systemClasses:
        if kls == cls:
            return n

    err = "attempted to determine name of unregistered system class: {}".format(cls)
    raise Exception(cls)


def getSystemClassByName(name):
    """
    Returns the system class associated with a given name.
    """
    assert (isinstance(name, str) or isinstance(name, unicode))
    return __systemClasses[name]


def destroyContainer(cntr):
    """
    Safely destroys a container by deallocating all attached resources
    (i.e., Docker containers, ports).
    """
    global __port_pool
    global __containers
    global __manager_lock

    assert (isinstance(cntr, systemContainer.SystemContainer) and not cntr is None)

    __manager_lock.acquire()
    port = cntr.port()
    __port_pool.add(port)
    __containers.remove(cntr)
    cntr.destroy()
    __manager_lock.release()


def createContainer(systm, image, verbose=False):
    """
    Constructs a fresh, ephemeral container for a given system using a
    specified Docker image.

    :param  systm:  the System object
    :param  image:  the name of the Docker image that should be used to spawn\
                    the container
    :param  verbose:    a flag indicating whether the outputs of the container \
                        should be printed to the stdout upon its destruction

    :returns    A new SystemContainer for the given system
    """
    global __port_pool
    global __containers
    global __manager_lock

    assert (isinstance(systm, system.System))

    __manager_lock.acquire()
    port = random.sample(__port_pool, 1)[0]
    __port_pool.remove(port)
    container = systemContainer.SystemContainer(systm, image, port, verbose=verbose)
    __containers.add(container)
    __manager_lock.release()

    return container
