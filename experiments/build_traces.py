#!/usr/bin/env python3
"""
This script is used to record execution traces for each mission within a
provided mission suite file.
"""
from typing import List, Iterator, Callable, Dict, Any
import os
import argparse
import concurrent.futures
import json
import logging
import contextlib
import functools
import signal, psutil

import bugzoo
import bugzoo.server
import houston
from houston.exceptions import ConnectionLostError, NoConnectionError

import settings

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)

DESCRIPTION = "Builds trace files for a given set of missions."

SandboxFactory = Callable[[bugzoo.BugZoo, bugzoo.Bug, houston.Mission], Iterator[houston.Sandbox]]


def kill_child_processes(parent_pid, sig=signal.SIGTERM):
    try:
        parent = psutil.Process(parent_pid)
    except psutil.NoSuchProcess:
        return
    children = parent.children(recursive=True)
    for process in children:
        if process.name() != "python":
            continue
        logger.debug("killing process %d", process.pid)
        process.send_signal(sig)


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    formatter = logging.Formatter('%(processName)s - %(message)s')
    log_to_stdout.setFormatter(formatter)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('snapshot', help='the name of the BugZoo snapshot')
    p.add_argument('missions', type=str,
                   help='path to a mission files.')
    p.add_argument('output', type=str,
                   help='the directory to which the traces should be written.')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity')
    p.add_argument('--coverage', action='store_true',
                   help='includes coverage information with each trace.')
    p.add_argument('--repeats', type=int, default=1,
                   help='number of traces to generate for each mission.')
    p.add_argument('--threads', type=int, default=1,
                   help='number of threads to use when building trace files.')
    return p.parse_args()


def trace(index: int,
          sandbox_factory: SandboxFactory,
          jsn_mission: Dict[str, Any],
          num_repeats: int,
          dir_output: str,
          collect_coverage: bool
          ) -> None:
    mission = houston.Mission.from_dict(json.loads(jsn_mission))

    # generate a (very-likely-to-be) "unique" ID for the mission
    uid = hex(abs(hash(mission)))[2:][:8]
    logger.info("generating trace for mission %d: %s", index, uid)
    filename = "{}.json".format(uid)
    filename = os.path.join(dir_output, filename)
    if os.path.exists(filename):
        logger.info("skipping trace: %d ('%s' already exists)", index, filename)
        return

    try:
        traces = []  # List[MissionTrace]
        for _ in range(num_repeats):
            with sandbox_factory() as sandbox:
                t = sandbox.run_and_trace(mission.commands, collect_coverage)
                traces.append(t)

        logger.debug("saving traces to file: %s", filename)
        with open(filename, 'w') as f:
            json.dump({'mission': mission.to_dict(),
                       'traces': [t.to_dict() for t in traces]},
                      f)
        logger.debug("saved trace to file: %s", filename)
    except (ConnectionLostError, NoConnectionError):
        logger.error("SITL crashed during trace %d: %s", index, uid)
    except (KeyboardInterrupt, SystemExit):
        logger.exception("received keyboard interrupt")
        raise
    except:
        logger.exception("failed to build trace %d: %s", index, uid)


@contextlib.contextmanager
def build_sandbox(client_bugzoo: bugzoo.Client,
                  snapshot: bugzoo.Bug,
                  jsn_mission: str
                  ) -> Iterator[houston.Sandbox]:
    mission = houston.Mission.from_dict(json.loads(jsn_mission))
    container = None  # type: Optional[bugzoo.Container]
    try:
        container = client_bugzoo.containers.provision(snapshot)
        sandbox_cls = mission.system.sandbox
        with sandbox_cls.for_container(client_bugzoo,
                                       container,
                                       mission.initial_state,
                                       mission.environment,
                                       mission.configuration) as sandbox:
            yield sandbox
    finally:
        if container:
            del client_bugzoo.containers[container.uid]


def build_traces(client_bugzoo: bugzoo.Client,
                 snapshot: bugzoo.Bug,
                 jsn_missions: List[str],
                 num_threads: int,
                 num_repeats: int,
                 dir_output: str,
                 collect_coverage: bool
                 ) -> None:
    futures = []
    with concurrent.futures.ProcessPoolExecutor(num_threads) as e:
        try:
            for i, jsn_mission in enumerate(jsn_missions):
                logger.debug("submitting mission %d", i)
                sandbox_factory = functools.partial(build_sandbox,
                                                    client_bugzoo,
                                                    snapshot,
                                                    jsn_mission)
                future = e.submit(trace,
                                  i,
                                  sandbox_factory,
                                  jsn_mission,
                                  num_repeats,
                                  dir_output,
                                  collect_coverage)
                futures.append(future)

            logger.debug("submitted all missions")
            logger.debug("waiting for missions to complete")
            concurrent.futures.wait(futures)
            logger.debug("finished executing all missions")
        except KeyboardInterrupt:
            logger.info("Received keyboard interrupt. Shutting down...")
            for fut in futures:
                logger.debug("Cancelling: %s", fut)
                fut.cancel()
                logger.debug("Cancelled: %s", fut.cancelled())
            logger.info("Shutting down the process pool")
            e.shutdown(wait=False)
            kill_child_processes(os.getpid())
            logger.info("Cancelled all jobs and shutdown executor.")
            client_bugzoo.containers.clear()
            logger.info("Killed all containers")


if __name__ == '__main__':
    args = parse_args()
    setup_logging(verbose=args.verbose)
    fn_missions = args.missions
    num_threads = args.threads
    num_repeats = args.repeats
    collect_coverage = args.coverage

    assert num_threads > 0
    assert num_repeats > 0

    os.makedirs(args.output, exist_ok=True)

    with open(fn_missions, 'r') as f:
        jsn = json.load(f)
    jsn_missions = [json.dumps(m) for m in jsn]

    with bugzoo.server.ephemeral() as client_bugzoo:
        snapshot = client_bugzoo.bugs[args.snapshot]
        build_traces(client_bugzoo, snapshot, jsn_missions, num_threads, num_repeats, args.output, collect_coverage)
