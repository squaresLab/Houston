from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import logging
import subprocess
import os
import time
import math

import argparse
import concurrent.futures


logger = logging.getLogger("houston")  # type: logging.Logger
logger.setLevel(logging.DEBUG)

COMMANDS=["MAV_CMD_NAV_WAYPOINT","MAV_CMD_NAV_TAKEOFF","MAV_CMD_NAV_LOITER_TURNS","MAV_CMD_NAV_LOITER_TIME","MAV_CMD_NAV_RETURN_TO_LAUNCH","MAV_CMD_NAV_LAND","MAV_CMD_NAV_SPLINE_WAYPOINT","MAV_CMD_DO_CHANGE_SPEED","MAV_CMD_DO_SET_HOME","MAV_CMD_DO_PARACHUTE"]

def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Run learn in parallel')
    parser.add_argument('train', type=str, action='store',
                       help='path to train directory.')
    parser.add_argument('number_of_seeds', type=int, action='store',
                        help='number of seeds')
    parser.add_argument('--threads', type=int, default=1,
                         help='number of threads')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')

    args = parser.parse_args()
    return args

def learn(data_dir: str,
          output: str,
          name: str,
          fuzzy: bool,
          seed: int):

    logger.info("started running for command {} seed {} type {}".format(name, seed, fuzzy))
    cmd = 'julia /home/afsoona/GBDTs.jl/learn.jl {} --output_dir {} --name {} 10 --seed {}'
    cmd = cmd.format(data_dir, output, name, seed)
    if fuzzy:
        cmd += ' --fuzzy'
    r = subprocess.call(cmd, shell=True)
    logger.info("finished running for command {} seed {} type {}".format(name, seed, fuzzy))
    return r


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    directory = args.train
    number_of_seeds = args.number_of_seeds
#    gbdts_data = os.path.join(directory, "GBDTs-data")
#    models_dir = os.path.join(directory, "models")


    results = []

    futures = []

    with concurrent.futures.ProcessPoolExecutor(args.threads) as e:
        for seed in range(1, number_of_seeds+1):
            model = os.path.join(directory, 'seed_{}'.format(seed), "models")
            if not os.path.exists(model):
                os.mkdir(model)
            for typ in ['fuzzy']:
                mt = os.path.join(model, typ)
                if not os.path.exists(mt):
                    os.mkdir(mt)
                if typ != 'noclust':
                    data_dir = os.path.join(directory, 'seed_{}'.format(seed), 'GBDTs-data')
                else:
                    data_dir = os.path.join(directory, 'noclust')
                if not os.path.exists(data_dir):
                    raise Exception("Data {} does not exist".format(data_dir))

                for cmd in COMMANDS:
                    ddir = os.path.join(data_dir, cmd)
                    if not os.path.exists(ddir):
                        logger.error("Data dir does not exist {}".format(ddir))
                        continue
                    typ_bool = False if typ == 'normal' else True
                    future = e.submit(learn, ddir, mt, cmd, typ_bool, seed)
                    futures.append(future)

    logger.debug("submitted all candidates")
    concurrent.futures.wait(futures)
    logger.debug("finished executing evaluating all mutants")
    
