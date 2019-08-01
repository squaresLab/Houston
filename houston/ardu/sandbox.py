from typing import Optional, Sequence
import time
import shlex
from timeit import default_timer as timer
import os
import sys
import threading
import logging

import docker
import dronekit
from bugzoo.client import Client as BugZooClient
from pymavlink import mavutil

from .home import HomeLocation
from .connection import CommandLong, MAVLinkConnection, MAVLinkMessage
from ..util import Stopwatch
from ..sandbox import Sandbox as BaseSandbox
from ..command import Command, CommandOutcome
from ..connection import Message
from ..mission import MissionOutcome
from ..trace import MissionTrace, CommandTrace, TraceRecorder
from ..exceptions import NoConnectionError, \
    ConnectionLostError, \
    PostConnectionSetupFailed, \
    VehicleNotReadyError

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)

TIME_LOST_CONNECTION = 5.0


def detect_lost_connection(f):
    """
    Decorates a given function such that any dronekit APIExceptions
    encountered during the execution of that function will be caught and thrown
    as ConnectionLostError exceptions.
    """
    def wrapped(*args, **kwargs):
        try:
            return f(*args, **kwargs)
        except dronekit.APIException:
            raise ConnectionLostError
    return wrapped


class Sandbox(BaseSandbox):
    def __init__(self,
                 *args,
                 home: Optional[HomeLocation] = None,
                 **kwargs
                 ) -> None:
        super().__init__(*args, **kwargs)
        self.__connection = None
        self.__sitl_thread = None
        self.__fn_log = None  # type: Optional[str]
        if home:
            self.__home = home
        else:
            self.__home = HomeLocation(latitude=-35.362938,
                                       longitude=149.165085,
                                       altitude=584,
                                       heading=270)

    @property
    def home(self) -> HomeLocation:
        return self.__home

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

    def has_connection(self) -> bool:
        """
        Checks whether a connection to the system running inside this
        sandbox exists.
        """
        return self.__connection is not None

    @property
    def vehicle(self,
                raise_exception: bool = True
                ) -> Optional[dronekit.Vehicle]:
        if not self.has_connection() and raise_exception:
            raise NoConnectionError()
        return self.connection.conn

    def read_logs(self) -> str:
        """
        Reads the contents of the log file for this sandbox.
        """
        assert self.__fn_log, "no log file created for sandbox."
        return self._bugzoo.files.read(self.container, self.__fn_log)

    def update(self, message: Message) -> None:
        with self.__state_lock:
            state = self.__state.evolve(message,
                                        self.running_time,
                                        self.connection)
            self.__state = state
            if self.recorder:
                self.recorder.record_state(state)
                self.recorder.record_message(message)

    def _launch_sitl(self,
                     name_bin: str = 'ardurover',
                     name_model: str = 'rover',
                     fn_param: str = '',  # FIXME what are the semantics of an empty string?  # noqa: pycodestyle
                     verbose: bool = True
                     ) -> None:
        """
        Launches the SITL inside the sandbox and blocks until its execution
        has finished.
        """
        bzc = self._bugzoo.containers

        # generate a temporary log file for the SITL
        self.__fn_log = bzc.mktemp(self.container)
        logger.debug("writing SITL output to: %s", self.__fn_log)

        name_bin = os.path.join("/opt/ardupilot/build/sitl/bin",  # FIXME
                                name_bin)
        speedup = self.configuration.speedup
        home = str(self.home)
        cmd = '{} --model "{}" --speedup "{}" --home "{}" --defaults "{}"'
        cmd = cmd.format(name_bin, name_model, speedup, home, fn_param)
        cmd = '{} >& {}'.format(cmd, shlex.quote(self.__fn_log))

        # add SITL prefix
        cmd = '{} {}'.format(self.prefix, cmd)

        logger.debug("launching SITL via: %s", cmd)

        # FIXME add non-blocking execution to BugZoo client API
        cmd = 'source /.environment && {}'.format(cmd)
        cmd = "/bin/bash -c {}".format(shlex.quote(cmd))
        logger.debug("wrapped command: %s", cmd)

        docker_client = docker.from_env()  # FIXME
        docker_api = docker_client.api
        resp = docker_api.exec_create(self.container.id,
                                      cmd,
                                      tty=True,
                                      stdout=True,
                                      stderr=True)
        output = docker_api.exec_start(resp['Id'], stream=verbose)
        logger.debug("started SITL")
        if verbose:
            for line in output:
                line = line.decode(sys.stdout.encoding).rstrip('\n')
                logger.getChild('SITL').debug(line)
            logger.debug("SITL finished")

    @detect_lost_connection
    def start(self,
              binary_name: str,
              model_name: str,
              param_file: str,
              verbose: bool = True
              ) -> None:
        """
        Launches the SITL inside this sandbox, and establishes a connection to
        the vehicle running inside the simulation. Blocks until SITL is
        launched and a connection is established.

        Raises:
            NoConnectionError: if a connection cannot be established.
            ConnectionLostError: if the connecton is lost before the vehicle
                is ready to receive commands.
            PostConnectionSetupFailed: if the post-connection setup phase
                failed.
            VehicleNotReadyError: if a timeout occurred before the vehicle was
                ready to accept commands.
        """
        stopwatch = Stopwatch()
        speedup = self.configuration.speedup
        timeout_set_mode = (15 / speedup + 2) + 30
        timeout_3d_fix = (10 / speedup + 2) + 30
        timeout_state = (90 / speedup + 2) + 30
        timeout_mavlink = 60

        bzc = self._bugzoo.containers
        args = (binary_name, model_name, param_file, verbose)
        self.__sitl_thread = threading.Thread(target=self._launch_sitl,
                                              args=args)
        self.__sitl_thread.daemon = True
        self.__sitl_thread.start()

        # establish connection
        protocol = 'tcp'
        port = 5760
        ip = str(bzc.ip_address(self.container))
        url = "{}:{}:{}".format(protocol, ip, port)
        logger.debug("connecting to SITL at %s", url)
        try:
            self.__connection = MAVLinkConnection(url,
                                                  {'update': self.update},
                                                  timeout=timeout_mavlink)
        except dronekit.APIException:
            raise NoConnectionError
        # wait for longitude and latitude to match their expected values, and
        # for the system to match the expected `armable` state.
        initial_lon = self.state_initial['longitude']
        initial_lat = self.state_initial['latitude']
        initial_armable = self.state_initial['armable']
        v = self.state_initial.__class__.variables

        # FIXME wait for 3D fix
        time.sleep(timeout_3d_fix)

        stopwatch.reset()
        stopwatch.start()
        while True:
            ready_lon = v['longitude'].eq(initial_lon, self.state['longitude'])
            ready_lat = v['latitude'].eq(initial_lat, self.state['latitude'])
            ready_armable = self.state['armable'] == initial_armable
            if ready_lon and ready_lat and ready_armable:
                break
            if stopwatch.duration > timeout_state:
                logger.error("latitude should be [%f] but was [%f]",
                             initial_lat, self.state['latitude'])
                logger.error("longitude should be [%f] but was [%f]",
                             initial_lon, self.state['longitude'])
                logger.error("armable should be [%s] but was [%s]",
                             initial_armable, self.state['armable'])
                raise VehicleNotReadyError
            time.sleep(0.05)

        if not self._on_connected():
            raise PostConnectionSetupFailed

        # wait until the vehicle is in GUIDED mode
        guided_mode = dronekit.VehicleMode('GUIDED')
        self.vehicle.mode = guided_mode
        stopwatch.reset()
        stopwatch.start()
        while self.vehicle.mode != guided_mode:
            if stopwatch.duration > timeout_set_mode:
                logger.error('vehicle is not in guided mode')
                raise VehicleNotReadyError
            time.sleep(0.05)

    def stop(self) -> None:
        logger.debug("Stopping SITL")
        bzc = self._bugzoo.containers
        if self.has_connection():
            self.connection.close()
        ps_cmd = 'ps aux | grep -i sitl | awk {\'"\'"\'print $2,$11\'"\'"\'}'

        out = bzc.command(self.container, ps_cmd)
        all_processes = out.output.splitlines()
        logger.debug("checking list of processes: %s", str(all_processes))
        for p in all_processes:
            if not p:
                continue
            pid, cmd = p.split(' ')

            is_sitl = cmd.startswith('/opt/ardupilot')
            if not is_sitl and self.prefix:
                is_sitl = cmd.startswith(self.prefix.split(' ')[0])
            logger.debug("cmd [%s]: %s", is_sitl, cmd)
            if is_sitl:
                bzc.command(self.container, "kill -2 {}".format(pid))
                logger.debug("killed process: %s", pid)
                break
        logger.debug("Killed it")
        logger.debug("Joining thread")
        self.__sitl_thread.join()
        logger.debug("Joined")
#       cmd = 'ps aux | grep -i sitl | awk {\'"\'"\'print $2\'"\'"\'} | xargs kill -2'  # noqa: pycodestyle
#       bzc.command(self.container, cmd, stdout=False, stderr=False)

    def _on_connected(self) -> bool:
        """
        Called immediately after a connection to the vehicle is established.
        """
        return True

    @detect_lost_connection
    def run_and_trace(self,
                      commands: Sequence[Command],
                      collect_coverage: bool = False
                      ) -> 'MissionTrace':
        """
        Executes a mission, represented as a sequence of commands, and
        returns a description of the outcome.

        Parameters:
            commands: the list of commands to be sent to the robot as
                a mission.
            collect_coverage: indicates whether or not coverage information
                should be incorporated into the trace. If True (i.e., coverage
                collection is enabled), this function expects the sandbox to be
                properly instrumented.

        Returns:
            a trace describing the execution of a sequence of commands.
        """
        config = self.configuration
        env = self.environment
        speedup = config.speedup
        timeout_command = 300 / speedup + 5
        timeout_arm = 10 / speedup + 5
        timeout_mission_upload = 20
        # the number of seconds for the delay added after DO commands
        do_delay = max(4, int(20 / speedup))
        with self.__lock:
            outcomes = []  # type: List[CommandOutcome]
            passed = True
            connection_lost = threading.Event()

            # FIXME The initial command should be based on initial state
            initial = dronekit.Command(0, 0, 0,
                                       0, 16, 0, 0,
                                       0.0, 0.0, 0.0, 0.0,
                                       -35.3632607, 149.1652351, 584)
            # delay to allow the robot to reach its stable state
            delay = dronekit.Command(0, 0, 0,
                                     3, 93, 0, 0,
                                     do_delay, -1, -1, -1,
                                     0, 0, 0)

            # converting from Houston commands to dronekit commands
            dronekitcmd_to_cmd_mapping = {}
            cmds = [initial]
            for i, cmd in enumerate(commands):
                dronekitcmd_to_cmd_mapping[len(cmds)] = i
                cmds.append(cmd.to_message().to_dronekit_command())
                # DO commands trigger some action and return.
                # we add a delay after them to see how they affect the state.
                if 'MAV_CMD_DO_' in cmd.__class__.uid:
                    dronekitcmd_to_cmd_mapping[len(cmds)] = i
                    cmds.append(delay)
            logger.debug("Final mission commands len: %d, mapping: %s",
                         len(cmds), dronekitcmd_to_cmd_mapping)

            # uploading the mission to the vehicle
            vcmds = self.vehicle.commands
            vcmds.clear()
            for cmd in cmds:
                vcmds.add(cmd)
            vcmds.upload(timeout=timeout_mission_upload)
            logger.debug("Mission uploaded")
            vcmds.wait_ready()

            # maps each wp to the final state and time when wp was reached
            wp_to_state = {}  # Dict[int, Tuple[State, float]]
            # [wp that has last been reached, wp running at the moment]
            last_wp = [0, 0]
            # used to synchronize rw to last_wp
            wp_lock = threading.Lock()
            # is set whenever a command in mission is done
            wp_event = threading.Event()

            # NOTE dronekit connection must not use its own heartbeat checking
            def heartbeat_listener(_, __, value):
                if value > TIME_LOST_CONNECTION:
                    connection_lost.set()
                    wp_event.set()
            self.vehicle.add_attribute_listener('last_heartbeat',
                                                heartbeat_listener)

            def check_for_reached(m):
                name = m.name
                message = m.message
                if name == 'MISSION_ITEM_REACHED':
                    logger.debug("**MISSION_ITEM_REACHED: %d", message.seq)
                    if message.seq == len(cmds) - 1:
                        logger.info("Last item reached")
                        with wp_lock:
                            last_wp[1] = int(message.seq) + 1
                            wp_event.set()
                elif name == 'MISSION_CURRENT':
                    logger.debug("**MISSION_CURRENT: %d", message.seq)
                    logger.debug("STATE: {}".format(self.state))
                    if message.seq > last_wp[1]:
                        with wp_lock:
                            if message.seq > last_wp[0]:
                                last_wp[1] = message.seq
                                logger.debug("SET EVENT")
                                wp_event.set()
                elif name == 'MISSION_ACK':
                    logger.debug("**MISSION_ACK: %s", message.type)

            self.connection.add_hooks({'check_for_reached': check_for_reached})

            stopwatch = Stopwatch()
            stopwatch.start()
            self.vehicle.armed = True
            while not self.vehicle.armed:
                if stopwatch.duration >= timeout_arm:
                    raise VehicleNotReadyError
                logger.debug("waiting for the rover to be armed...")
                self.vehicle.armed = True
                time.sleep(0.1)

            # starting the mission
            self.vehicle.mode = dronekit.VehicleMode("AUTO")
            initial_state = self.state
            start_message = CommandLong(
                0, 0, 300, 0, 1, len(cmds) + 1, 0, 0, 0, 0, 4)
            self.connection.send(start_message)
            logger.debug("sent mission start message to vehicle")
            time_start = timer()

            wp_to_traces = {}
            with self.record() as recorder:
                while last_wp[0] <= len(cmds) - 1:
                    logger.debug("waiting for command")
                    not_reached_timeout = wp_event.wait(timeout_command)
                    logger.debug("Event set %s", last_wp)
                    if not not_reached_timeout:
                        logger.error("Timeout occured %d", last_wp[0])
                        break
                    if connection_lost.is_set():
                        logger.error("Connection to vehicle was lost.")
                        raise ConnectionLostError
                    with wp_lock:
                        # self.observe()
                        logger.info("last_wp: %s len: %d",
                                    str(last_wp),
                                    len(cmds))
                        logger.debug("STATE: {}".format(self.state))
                        current_time = timer()
                        time_passed = current_time - time_start
                        time_start = current_time
                        states, messages = recorder.flush()
                        if last_wp[0] > 0:
                            cmd_index = dronekitcmd_to_cmd_mapping[last_wp[0]]
                            wp_to_state[cmd_index] = (self.state, time_passed)
                            cmd = commands[cmd_index]
                            trace = CommandTrace(cmd, states)
                            wp_to_traces[cmd_index] = trace

                        last_wp[0] = last_wp[1]
                        wp_event.clear()

            self.connection.remove_hook('check_for_reached')
            logger.debug("Removed hook")

            coverage = None
            if collect_coverage:
                # if appropriate, store coverage files
                self.__flush_coverage()
                coverage = self.__get_coverage()

            traces = [wp_to_traces[k] for k in sorted(wp_to_traces.keys())]
            return MissionTrace(tuple(traces), coverage)

    def __get_coverage(self) -> "FileLineSet":
        """
        Copies gcda files from /tmp/<directory> to /opt/ardupilot
        (where the source code is) and collects coverage results.
        """
        bzc = self._bugzoo.containers

        coverage = bzc.extract_coverage(self.container)
        return coverage

    def __flush_coverage(self) -> None:
        """
        Sends a SIGUSR1 signal to ardupilot processes running in the
        container. They will flush gcov data into gcda files that
        will be copied to /tmp/<directory> for later use.
        """
        bzc = self._bugzoo.containers
        ps_cmd = 'ps aux | grep -i sitl | awk {\'"\'"\'print $2,$11\'"\'"\'}'

        out = bzc.command(self.container, ps_cmd)
        all_processes = out.output.splitlines()
        logger.debug("checking list of processes: %s", str(all_processes))
        for p in all_processes:
            if not p:
                continue
            pid, cmd = p.split(' ')
            if cmd.startswith('/opt/ardupilot'):
                bzc.command(self.container, "kill -10 {}".format(pid))
                break
