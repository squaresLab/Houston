import sys


class TimeoutError(Exception):
    @staticmethod
    def produce(msg=None):
        raise TimeoutError(msg)


def printflush(s):
    print(s)
    sys.stdout.flush()
