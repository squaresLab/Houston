"""
This script is responsible for producing a requested number of mutants for use
in a ground truth evaluation.
"""
from typing import List, Iterator, Tuple, Set, Optional
import contextlib
import logging
import argparse
import random
import functools

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import PreservedScalarString
import yaml
import bugzoo
import boggart
import rooibos

logger = logging.getLogger(__name__)  # type: logging.Logger
logger.setLevel(logging.DEBUG)

MUTABLE_FILES = [
    'ArduCopter/mode.cpp',
    'ArduCopter/mode_auto.cpp',
    'libraries/AP_Common/Location.cpp',
    'libraries/AP_Mission/AP_Mission.cpp',
    'ArduCopter/ArduCopter.cpp',
    'ArduCopter/AP_State.cpp',
    'ArduCopter/Attitude.cpp',
    'ArduCopter/commands.cpp',
    'ArduCopter/crash_check.cpp',
    'ArduCopter/motors.cpp',
    'ArduCopter/sensors.cpp',
    'libraries/AP_Parachute/AP_Parachute.cpp'
]

DESCRIPTION = \
"""
Generates a specified number of acceptable mutants for the purpose of a later
ground truth evaluation.
"""

def setup_logging() -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG)
    logging.getLogger('bugzoo').addHandler(log_to_stdout)
    logging.getLogger('boggart').addHandler(log_to_stdout)
    logging.getLogger('rooibos').addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger(__name__).addHandler(log_to_stdout)


def get_args():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    parser.add_argument('number', type=int,
                        help="the desired number of acceptable mutants to generate.")
    parser.add_argument('--snapshot', type=str, default='arducopter:3.6.4',
                        help='the name of the BugZoo snapshot that should be mutated.')
    parser.add_argument('--output', type=str, default='mutants.yml',
                        help="the file to which the mutants should be written.")
    return parser.parse_args()


@contextlib.contextmanager
def launch_servers() -> Iterator[Tuple[bugzoo.Client, boggart.Client]]:
    logger.debug("launching BugZoo")
    with bugzoo.server.ephemeral(port=6060) as client_bugzoo:
        logger.debug("launching Rooibos")
        with rooibos.ephemeral_server(port=8888) as client_rooibos:
            logger.debug("launching Boggart")
            with boggart.server.ephemeral() as client_boggart:
                logger.debug("launched all services")
                yield client_bugzoo, client_boggart


def all_mutations(client_bugzoo: bugzoo.Client,
                  client_boggart: boggart.Client,
                  snapshot: bugzoo.Bug
                  ) -> List[boggart.Mutation]:
    """
    Generates the set of all possible syntactic mutations to a given version of
    ArduPilot, provided as a BugZoo snapshot.
    """
    # FIXME we also need to decide which mutation operators to use.
    operators = [
        client_boggart.operators['flip-boolean-operator'],
        client_boggart.operators['flip-arithmetic-operator'],
        client_boggart.operators['flip-relational-operator']
    ]
    mutations = []
    for filename in MUTABLE_FILES:
        logger.debug("finding mutations to file [%s]", filename)
        generator = client_boggart.mutations(
            snapshot,
            filename,
            operators=operators,
            language=client_boggart.languages['C++'])
        mutations_to_file = list(generator)
        logger.debug("found %d mutations to file [%s]",
                     len(mutations_to_file), filename)
        mutations += mutations_to_file
    return mutations


def is_acceptable_mutant(client_bugzoo: bugzoo.Client,
                         client_boggart: boggart.Client,
                         snapshot: bugzoo.Bug,
                         mutation: boggart.Mutation
                         ) -> bool:
    """
    Determines whether a given mutant is suitable for use in a ground truth
    evaluation.
    """
    mutant = None  # type: Optional[boggart.Mutant]
    try:
        mutant = client_boggart.mutate(snapshot, [mutation])

        # TODO filter out program crashes

        # TODO keep semantic mutants
        return True

    except boggart.exceptions.BoggartException:
        logger.exception("failed to build mutant: %s", mutation)
        return False
    finally:
        if mutant:
            del client_boggart.mutants[mutant.uuid]


def main():
    setup_logging()
    args = get_args()
    fn_output = args.output
    num_requested = args.number
    name_snapshot = args.snapshot

    # find and shuffle the set of all candidate syntactic mutations
    with launch_servers() as (client_bugzoo, client_boggart):
        snapshot = client_bugzoo.bugs[name_snapshot]
        is_acceptable = \
            functools.partial(is_acceptable_mutant, client_bugzoo, client_boggart, snapshot)
        candidates = all_mutations(client_bugzoo, client_boggart, snapshot)
        random.shuffle(candidates)

        acceptable = []  # type: List[str]
        for mutation in candidates:
            if len(acceptable) == num_requested:
                break
            if is_acceptable(mutation):
                diff = str(client_boggart.mutations_to_diff(snapshot, [mutation]))
                acceptable.append(diff)

        yml = [{'diff': PreservedScalarString(d)} for d in acceptable]
        with open(fn_output, 'w') as f:
            YAML().dump(yml, f)


if __name__ == '__main__':
    main()
