import dronekit
import time
import os
import sys
import threading
import houston.sandbox
from houston.mission import Mission
from typing import Optional


class NoConnectionError(BaseException):
    """
    Thrown when there is no connection to the vehicle running inside a sandbox.
    """
    def __init__(self):
        super().__init__("No connection to vehicle inside sandbox.")


class Sandbox(houston.sandbox.Sandbox):
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

    def _launch_sitl(self, binary_name: str = "ardurover", model_name: str = "rover", param_file: str = "", verbose: bool = True) -> None:
        """
        Launches the SITL inside the sandbox and blocks until its execution
        has finished.
        """
        # TOOD: use param_files
        home = "-35.362938,149.165085,584,270"
        cmd = '/experiment/source/build/sitl/bin/{} --model "{}" --speedup "{}" --home "{}"'
        cmd = cmd.format(binary_name, model_name, self.system.speedup, home)

        if not verbose:
            self.bugzoo.command(cmd, stdout=False, stderr=False, block=False)
            return

        execution_response = self.bugzoo.command(cmd, stdout=True, stderr=True, block=False)
        for line in execution_response.output:
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
        self.__sitl_thread = threading.Thread(target=self._launch_sitl,
                                              args=(binary_name, model_name,
                                              param_file, verbose))
        self.__sitl_thread.daemon = True
        self.__sitl_thread.start()

        # establish connection
        # TODO fix connection issue
        from pymavlink import mavutil
        protocol = 'tcp'
        port = 5760
        url = "{}:{}:{}".format(protocol, str(self.bugzoo.ip_address), port)
        dummy_connection = mavutil.mavlink_connection(url)
        time.sleep(10)
        dummy_connection.close()
        time.sleep(5)
        self.__connection = dronekit.connect(url, wait_ready=True)

        # wait until vehicle is ready to test
        self.__connection.wait_ready('autopilot_version')

        # wait for longitude and latitude to match their expected values, and
        # for the system to match the expected `armable` state.
        initial_lon = mission.initial_state['longitude']
        initial_lat = mission.initial_state['latitude']
        while True:
            observed = self.observe(0.0)
            if self.system.variable('longitude').eq(initial_lon, observed['longitude']) and \
               self.system.variable('latitude').eq(initial_lat, observed['latitude']) and \
               observed['armable'] == mission.initial_state['armable']:
                break
            time.sleep(0.05)

        # wait until the vehicle is in GUIDED mode
        # TODO: add timeout
        guided_mode = dronekit.VehicleMode('GUIDED')
        self.__connection.mode = guided_mode
        while self.__connection.mode != guided_mode:
            time.sleep(0.05)

    def _stop(self) -> None:
        """
        Closes any connection to a simulated vehicle inside the sandbox, before
        terminating the associated simulator.
        """
        # close the connection
        if self.connection:
            self.connection.close()
        # close the SITL
        self.bugzoo.command('killall5 -9 build/sitl/bin', stdout=False, stderr=False, block=False)
