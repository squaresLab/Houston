__all__ = ['mutation_to_uid']

import argparse
from ruamel.yaml import YAML

DESCRIPTION = """
Creates a yaml file that only includes mutants in the list.
""".strip()


def get_args():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    parser.add_argument('input', type=str,
                        help="path to input ground truth database file.")
    parser.add_argument('list', type=str,
                        help="path to list of mutants file.")
    parser.add_argument('output', type=str,
                        help="path to output ground truth database file.")
    return parser.parse_args()


if __name__ == '__main__':
    args = get_args()
    with open(args.input, 'r') as f:
        db = YAML().load(f)
    with open(args.list, 'r') as f:
        m_list = YAML().load(f)

    yes = m_list['yes']
    entries = [entry for entry in db['entries'] if entry['uid'] in yes]
    db['entries'] = entries

    with open(args.output, 'w') as f:
        YAML().dump(db, f)
