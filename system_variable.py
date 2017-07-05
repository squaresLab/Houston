"""
Description of system variables goes here!

* How do we use them?
* What are they for?
"""
class SystemVariable(object):

    """
    Constructs a new system variable
    """
    def __init__(self, getter):
        self.__getter = getter

    """
    Inspects the current state of this system variable
    """
    def read(self):
        return self.__getter()
