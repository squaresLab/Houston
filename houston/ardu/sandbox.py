import dronekit
import time
import os
from houston.mission import Mission
from houston.sandbox import Sandbox
from typing import Optional


class NoConnectionError(BaseException):
    """
    Thrown when there is no connection to the vehicle running inside a sandbox.
    """
    def __init__(self):
        super().__init__("No connection to vehicle inside sandbox.")


class ArduSandbox(Sandbox):
    def __init__(self, system: 'ardu.BaseSystem') -> None:
        super().__init__(system)
        self.__connection = None
        self.__sitl_thread = None

    @property
    def connection(self,
                   raise_exception: bool = True
                   ) -> Optional[dronekit.Vehicle]:
        """
        Uses dronekit to return a connection to the system running inside
        this sandbox.

        Raises:
            NoConnectionError: if there is no connection to the system running
                inside this sandbox.
        """
        if self.__connection is None and raise_exception:
            raise NoConnectionError()
        return self.__connection

    def _launch_sitl(self, verbose: bool = True) -> None:
        """
        Launches the SITL inside the sandbox and blocks until its execution
        has finished.
        """
        # TOOD: support other systems
        model = "rover"
        home = "-35.362938,149.165085,584,270"
        cmd = 'build/sitl/bin/ardurover --model "{}" --speedup "{}" --home "{}"'
        cmd = cmd.format(model, self.system.speedup, home)

        # TODO: use BugZoo commands
        if not verbose:
            self.bugzoo.exec_run(cmd, detach=True)
            return

        (_, output_stream) = self.bugzoo.exec_run(cmd, stream=True)
        for line in output_stream:
            line = line.decode(sys.stdout.encoding).rstrip('\n')
            print(line, flush=True)

    def _start(self,
               mission: Mission,
               binary_name: str,
               model_name: str,
               param_file: str,
               verbose: bool = True
               ) -> None:
        """
        Launches the SITL inside this sandbox, and establishes a connection to
        the vehicle running inside the simulation. Blocks until SITL is launched
        and a connection is established.
        """
        # launch SITL
        # TODO: use supplied (binary_name, model_name, param_file) arguments
        self.__sitl_thread = threading.Thread(target=ArduBox.launch_sitl,
                                              args=(self, verbose))
        self.__sitl_thread.daemon = True
        self.__sitl_thread.start()

        # TODO: establish connection

        # wait until vehicle is ready to test
        self.__connection.wait_ready('autopilot_version')

        # wait for longitude and latitude to match their expected values, and
        # for the system to match the expected `armable` state.
        initial_lon = mission.initial_state['longitude']
        initial_lat = mission.initial_state['latitude']
        while True:
            observed = self.observe()
            if self.system.variable('longitude').eq(initial_lon, observed['longitude']) and \
               self.system.variable('latitude').eq(initial_lat, observed['latitude']) and \
               observed['armable'] == mission.initial_state['armable']:
                break
            time.sleep(0.05)

        # wait until the vehicle is in GUIDED mode
        # TODO: add timeout
        guided_mode = dronekit.VehicleMode('GUIDED')
        self.__connection.mode = guided_mode
        while self.vehicle.mode != guided_mode:
            time.sleep(0.05)

    def _stop(self) -> None:
        """
        Closes any connection to a simulated vehicle inside the sandbox, before
        terminating the associated simulator.
        """
        # TODO: close the connection

        # TODO: close the SITL
