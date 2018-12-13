__all__ = ['Recorder', 'NoFileSetError']

from typing import Type, FrozenSet, Dict, Any, List, Optional
import attr
import logging

import json
import threading

from .state import State
from .command import Command

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)


# TODO Exception to Houston Exception (#147)
class NoFileSetError(Exception):
    """
    Thrown when writing to file is requested but filename is not
    set.
    """
    def __init__(self):
        super().__init__("No file is set for the recorder.")


class Recorder(object):
    """
    Recorders are used to keep tracks of states
    created in the execution and write them to files.
    """
    def __init__(self,
                 states: Optional[List[State]] = None,
                 filename: str = ''
                 ) -> None:
        self.__states = states if states else []
        self.__filename = filename
        self.__lock = threading.Lock()
        self.__file_lock = threading.Lock()

    @property
    def states(self) -> List[State]:
        return self.__states

    @property
    def filename(self) -> str:
        return self.__filename

    def add(self, state: State):
        with self.__lock:
            self.__states.append(state)

    def write_and_flush(self,
                        command: Command,
                        index: int
                        ) -> List[Dict[str, Any]]:
        if not self.filename:
            raise NoFileSetError()
        with self.__lock:
            states = list(map(State.to_dict, self.__states))
            self.__states = []
        with self.__file_lock:
            with open(self.filename, 'a') as f:
                info = {'command': command.to_dict(),
                        'index': index,
                        'states': states}
                json.dump(info, f)
                f.write('\n')
        return states

    def flush(self) -> List[State]:
        with self.__lock:
            states = self.__states
            self.__states = []
            return states

    def write(self, string: str) -> bool:
        if not self.filename:
            raise NoFileSetError()
        with self.__file_lock:
            with open(self.filename, 'a') as f:
                f.write(string)
