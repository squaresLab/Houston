__all__ = ['Sandbox']

import os

from ..sandbox import Sandbox as ArduSandbox
from ...test import Test


class Sandbox(ArduSandbox):
    def _start(self, test: Test) -> None:
        # FIXME #66
        fn_param = os.path.join(self.snapshot.source_dir,
                                'Tools/autotest/default_params/rover.parm')
        super()._start(test,
                       binary_name='ardurover',
                       model_name='rover',
                       param_file=fn_param)
