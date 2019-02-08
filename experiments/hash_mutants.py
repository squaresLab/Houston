__all__ = ['mutation_to_uid']

import argparse
import hashlib

from ruamel.yaml import YAML

DESCRIPTION = """
Adds unique identifiers to each mutant within a ground truth database file.
""".strip()


def mutation_to_uid(diff: str) -> str:
    m = hashlib.sha512()
    m.update(diff.encode())
    uid = m.hexdigest()[:24]
    return uid


def get_args():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    parser.add_argument('input', type=str,
                        help="path to input ground truth database file.")
    parser.add_argument('output', type=str,
                        help="path to output ground truth database file.")
    return parser.parse_args()


if __name__ == '__main__':
    args = get_args()
    with open(args.input, 'r') as f:
        db = YAML().load(f)

    for entry in db['entries']:
        entry['uid'] = mutation_to_uid(entry['diff'])
        entry['diff'] = entry['diff']

    with open(args.output, 'w') as f:
        YAML().dump(db, f)
