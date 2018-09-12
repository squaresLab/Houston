__all__ = ['Sandbox']

import os

from ..sandbox import Sandbox as ArduSandbox
from ...mission import Mission


class Sandbox(ArduSandbox):
    def _start(self, mission: Mission) -> None:
        # FIXME #66
        fn_param = os.path.join(self.container.source_dir,
                                'Tools/autotest/default_params/rover.parm')
        super(Sandbox, self)._start(
            mission,
            binary_name='ardurover', model_name='rover', param_file=fn_param)
