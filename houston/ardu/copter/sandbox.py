__all__ = ['Sandbox']

import os

from ..sandbox import Sandbox as ArduSandbox
from ...mission import Mission


class Sandbox(ArduSandbox):
    def _start(self, mission: Mission) -> None:
        # FIXME #66
        fn_param = os.path.join(self.container.source_dir,
                                'Tools/autotest/default_params/copter.parm')
        super(Sandbox, self)._start(
            mission,
            binary_name='arducopter',
            model_name='quad',
            param_file=fn_param)

    def _post_connection_setup(self):
        if not self.connection:
            return False

        self.connection.parameters['DISARM_DELAY'] = 0
        self.connection.parameters['RTL_ALT'] = 0

        # wait until copter is in desired configuration
        # TODO This code doesn't work in python 3
        #   while True:
        #       if self.connection.parameters['DISARM_DELAY'] == 0 and \
        #          self.connection.parameters['RTL_ALT'] == 0:
        #           break
        #       time.sleep(0.05)
        return True
