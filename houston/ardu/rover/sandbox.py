from houston.ardu.sandbox import Sandbox as ArduSandbox
from houston.mission import Mission

class Sandbox(ArduSandbox):
    def start(self, mission: Mission) -> None:
        self._start(mission,  binary_name='ardurover',
                                    model_name='rover',
                                    param_file='rover')
