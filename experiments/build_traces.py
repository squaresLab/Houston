#!/usr/bin/env python3
"""
This script is used to record execution traces for each mission within a
provided mission suite file.
"""
from typing import List
import os
import argparse
import concurrent.futures
import json
import logging
import contextlib

import bugzoo
import bugzoo.server
import houston

import settings

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)

DIR_TRACES = "traces"
SNAPSHOT_NAME = "ardubugs:742cdf6b"
DESCRIPTION = "Builds trace files for a given set of missions."


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('missions', type=str,
                   help='path to a mission files.')
    p.add_argument('--verbose', action='store_true',
                   help='increases logging verbosity')
    p.add_argument('--threads', type=int, default=1,
                   help='number of threads to use when building trace files.')
    return p.parse_args()


def trace(client_bugzoo: bugzoo.Client,
          container: bugzoo.Container,
          index: int,
          mission: houston.mission.Mission
          ) -> None:
    # generate a (very-likely-to-be) "unique" ID for the mission
    uid = hex(abs(hash(mission)))[2:][:8]
    logger.info("generating trace for mission %d: %s", index, uid)
    filename = "{}.json".format(uid)
    filename = os.path.join(DIR_TRACES, filename)
    if os.path.exists(filename):
        logger.info("skipping trace: %d ('%s' already exists)", index, filename)
        return

    try:
        sandbox_cls = mission.system.sandbox
        with sandbox_cls.for_container(client_bugzoo,
                                       container,
                                       mission.initial_state,
                                       mission.environment,
                                       mission.configuration) as sandbox:
            trace = sandbox.run_and_trace(mission.commands)
            logger.debug("saving trace to file: %s", filename)
            trace.to_file(filename)
            logger.debug("saved trace to file: %s", filename)
    except (KeyboardInterrupt, SystemExit):
        raise
    except:
        logger.exception("failed to build trace %d: %s", index, uid)


def build_traces(client_bugzoo: bugzoo.Client,
                 snapshot: bugzoo.Bug,
                 missions: List[houston.Mission],
                 num_threads: int
                 ) -> None:
    containers = []
    futures = []
    try:
        logger.info("preparing containers")
        for _ in range(num_threads):
            container = client_bugzoo.containers.provision(snapshot)
            client_bugzoo.containers.prepare_for_coverage(container)
            containers.append(container)
        logger.info("prepared containers")

        with concurrent.futures.ThreadPoolExecutor(num_threads) as e:
            for i, mission in enumerate(missions):
                logger.debug("submitting mission %d", i)
                container = containers[i % num_threads]
                future = e.submit(trace, client_bugzoo, container, i, mission)
                futures.append(future)
        logger.debug("submitted all missions")
        logger.debug("waiting for missions to complete")
        concurrent.futures.wait(futures)
        logger.debug("finished executing all missions")
    finally:
        for c in containers:
            del client_bugzoo.containers[c.uid]


if __name__ == '__main__':
    args = parse_args()
    setup_logging(verbose=args.verbose)
    fn_missions = args.missions
    num_threads = args.threads

    assert num_threads > 0

    os.makedirs(DIR_TRACES, exist_ok=True)

    with open(fn_missions, 'r') as f:
        jsn = json.load(f)
    missions = [houston.Mission.from_dict(d) for d in jsn]

    # FIXME use an ephemeral server! (bugzoo.server.ephemeral())
    client_bugzoo = bugzoo.BugZoo()
    try:
        snapshot = client_bugzoo.bugs[SNAPSHOT_NAME]
        build_traces(client_bugzoo, snapshot, missions, num_threads)
    finally:
        client_bugzoo.shutdown()
