from houston.ardu.sandbox import Sandbox as ArduSandbox
from houston.mission import Mission

class Sandbox(ArduSandbox):
    def _start(self, mission: Mission) -> None:
        super(self).start(mission,  binary_name='ardurover',
                                    model_name='rover',
                                    param_file='rover')
