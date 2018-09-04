from ..sandbox import Sandbox as ArduSandbox
from ...mission import Mission


class Sandbox(ArduSandbox):
    def _start(self, mission: Mission) -> None:
        # FIXME #50
        fn_param = '/experiment/source/Tools/autotest/default_params/rover.parm'  # noqa: pycodestyle
        super(Sandbox, self)._start(
            mission,
            binary_name='ardurover', model_name='rover', param_file=fn_param)
