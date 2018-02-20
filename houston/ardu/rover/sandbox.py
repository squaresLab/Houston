import houston.ardu.sandbox
from houston.mission import Mission

class Sandbox(houston.ardu.sandbox.Sandbox):
    def _start(self, mission: Mission) -> None:
        super(self).setup(mission,  binary_name='ardurover',
                                    model_name='rover',
                                    param_file='rover')
