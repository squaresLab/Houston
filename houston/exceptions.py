from typing import Type


class HoustonException(Exception):
    """
    Base class used by all of Houston's exceptions.
    """


class NoFileSetError(HoustonException):
    """
    Thrown when writing to mission trace file has been requested, but no
    filename has been set.
    """
    def __init__(self):
        super().__init__("No file is set for the recorder.")


class InvalidExpression(HoustonException):
    """
    The s-expression does not have a valid format.
    """
    def __init__(self) -> None:
        msg = "The s-expression does not have a valid format."
        super().__init__(msg)


class UnsupportedVariableType(HoustonException):
    """
    Houston and/or Z3 do not support variables of a given Python type.
    """
    def __init__(self, type_py: Type) -> None:
        msg = "Houston and/or Z3 does not support variable type: {}"
        msg = msg.format(type_py.__name__)
        super().__init__(msg)
