import argparse
import json

DESCRIPTION = "Extracts the trace for a mutant from a ground truth file."


def parse_args():
    p = argparse.ArgumentParser(description=DESCRIPTION)
    p.add_argument('file', type=str, help='path to ground truth file.')
    p.add_argument('index', type=int, help='index of mutant within file.')
    return p.parse_args()


def main() -> None:
    args = parse_args()

    with open(args.file, 'r') as f:
        jsn = json.load(f)
        jsn = jsn['entries'][args.index]

    jsn = {'mission': jsn['mission'],
           'traces': [jsn['trace']]}

    print(json.dumps(jsn, indent=2))


if __name__ == '__main__':
    main()
