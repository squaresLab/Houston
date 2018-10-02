__all__ = ['Sandbox']

import os

from .state import State
from ..sandbox import Sandbox as ArduSandbox
from ...test import Test


class Sandbox(ArduSandbox):
    def _start(self, test: Test) -> None:
        # FIXME #66
        fn_param = os.path.join(self.snapshot.source_dir,
                                'Tools/autotest/default_params/copter.parm')
        super()._start(test,
                       binary_name='arducopter',
                       model_name='quad',
                       param_file=fn_param)

    def _post_connection_setup(self):
        if not self.connection:
            return False

        # FIXME Python 3 incompatibility in pymavlink (see #68)
        # self.connection.parameters['DISARM_DELAY'] = 0
        # self.connection.parameters['RTL_ALT'] = 0

        # wait until copter is in desired configuration
        # TODO This code doesn't work in python 3
        #   while True:
        #       if self.connection.parameters['DISARM_DELAY'] == 0 and \
        #          self.connection.parameters['RTL_ALT'] == 0:
        #           break
        #       time.sleep(0.05)
        return True
