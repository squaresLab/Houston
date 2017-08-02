"""
A registry of systems known to Houston, indexed by their identifiers.
"""
__systems = {}

"""
The pool of ports that are open and available to be used.
"""
__port_pool = set(i for i in range(500, 1000))


def registerSystem(system):
    """
    Registers a system with Houston.

    @TODO   we could perform this automatically using magic methods / class hooks
    """
    global __systems
    assert(isinstance(system, system.System) and not system is None)
    iden = system.identifier()
    if iden in __systems:
        raise Error("system already registered with name: {}".format(iden))
    __systems[iden] = system


def getSystem(identifier):
    """
    Returns the system associated with a given identifier.
    """
    return __systems[identifier]


def createContainer(system):
    pass
