from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import logging
import subprocess
import pexpect
import tempfile
import os
import json
import csv
import attr
import functools
import time

import argparse
import concurrent.futures

from ruamel.yaml import YAML

from ground_truth import DatabaseEntry
from compare_traces import load_file
from hash_mutants import mutation_to_uid

from enum import Enum

logger = logging.getLogger("houston")  # type: logging.Logger
logger.setLevel(logging.DEBUG)


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.addHandler(log_to_stdout)
    logging.getLogger('houston').addHandler(log_to_stdout)

@attr.s
class VerifiedEntry(object):
    fn = attr.ib(type=str)
    verified = attr.ib(type=Tuple[str, ...])

    def to_dict(self):
        return {'fn': self.fn,
                'verified': [res for res in self.verified]}


@attr.s
class NewDatabaseEntry(object):
    diff = attr.ib(type=str)
    fn_inconsistent_traces = attr.ib(type=Tuple[Tuple[VerifiedEntry, VerifiedEntry], ...])

    def to_dict(self):
        return {'diff': self.diff,
                'uid': mutation_to_uid(self.diff),
                'inconsistent': [{'oracle': o.to_dict(), 'trace': t.to_dict()} for o, t in self.fn_inconsistent_traces]}

class Status:
    ACCEPTED = 'ACCEPTED'
    REJECTED = 'REJECTED'
    UNSPECIFIED = 'UNSPECIFIED'
    PARTIAL = 'PARTIAL'


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Validate test traces')
    parser.add_argument('database', type=str, action='store',
                       help='path to test database yaml file.')
    parser.add_argument('models_dir', type=str, action='store',
                        help='path to directory with learned models.')
    parser.add_argument('GBDTs_path', type=str, action='store',
                        help='path to GBDTs.')
    parser.add_argument('--threshold', type=float, action='store',
                        default=0.4,
                        help='threshold for accepting a trace')
    parser.add_argument('--ignore-cat', action='store_true',
                        default=False,
                        help='ignore categorical fields of the data.')
    parser.add_argument('--separate-params', action='store_true',
                        default=False,
                        help='put parameters in a separate file')
    parser.add_argument('output', action='store', type=str,
                        help='the file where the results will be stored')
    parser.add_argument('--threads', type=int, default=1,
                         help='number of threads')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')

    args = parser.parse_args()
    return args


def parse_data(all_data):
    cmd_based_dict = {}
    result = []
    for i, m in enumerate(all_data):
        result.append({'gt': [], 'mu': []})
        for j in range(len(m["gt"])):
            trace = m["gt"][j]
            result[i]['gt'].append([])
            for k in range(len(trace['commands'])):
                result[i]['gt'][j].append(Status.UNSPECIFIED)
                c = trace['commands'][k]
                c_type = c['command']['type']
                typ = cmd_based_dict.get(c_type)
                if not typ:
                    cmd_based_dict[c_type] = [(i, 'gt', j, k),]
                else:
                    typ.append((i, 'gt', j, k))
        for j in range(len(m["mu"])):
            trace = m["mu"][j]
            result[i]['mu'].append([])
            for k in range(len(trace['commands'])):
                result[i]['mu'][j].append(Status.UNSPECIFIED)
                c = trace['commands'][k]
                c_type = c['command']['type']
                typ = cmd_based_dict.get(c_type)
                if not typ:
                    cmd_based_dict[c_type] = [(i, 'mu', j, k),]
                else:
                    typ.append((i, 'mu', j, k))
    return cmd_based_dict, result

def check_against_model(all_data, cmd_based_dict, result, models_dir, GBDTs_path, ignore_cat, separate_params, threshold=0.4):
    julia_p = pexpect.spawn('julia {}'.format(str(os.path.join(GBDTs_path, 'test.jl'))))
    stdout = julia_p.readline()
    while not stdout or not "Ready" in stdout.decode():
        time.sleep(5)
        stdout = julia_p.readline()

    for cmd in cmd_based_dict.keys():
        model = os.path.join(models_dir, "{}.jld".format(cmd[len('factory.'):]))
        if not os.path.isfile(model):
            logger.info("Model doesn't exist for command {}".format(cmd))
            continue
        dirpath = tempfile.mkdtemp()
        logger.debug("tempdir: {}".format(dirpath))
        indexes = []
        l = 1
        keys = []
        dict_writer = None
        with open(os.path.join(dirpath, "data.csv.gz"), "w") as output_file:
            for i, t, j, k in cmd_based_dict[cmd]:
                logger.debug("{} {} {} {}".format(i, t, j, k))
                indexes.append(str(l))
                c = all_data[i][t][j]['commands'][k]
                states = c['states']
                if not dict_writer:
                    if not ignore_cat:
                        keys = list(c['states'][0].keys())
                    else:
                        keys = [n for n in sorted(c['states'][0]) if type(c['states'][0][n]) == float]
                if not separate_params:
                    if not ignore_cat:
                        p = {'p_{}'.format(key): v for key, v in c['command']['parameters'].items()}
                    else:
                        p = {'p_{}'.format(key): v for key, v in c['command']['parameters'].items() if type(v) not in [bool, str]}
                    for s in states:
                        s.update(p)
                    if not ignore_cat:
                        for s in states:
                            if "mode" in s:
                                s["mode"] = 0 if s["mode"] == "AUTO" else 1 # TODO fix this. There are other modes that AUTO and GUIDED
                            for key,v in s.items():
                                if type(v) == bool:
                                    s[key] = int(v)
                if not dict_writer:
                    if not separate_params:
                        keys.extend(sorted(p.keys()))
                    dict_writer = csv.DictWriter(output_file, keys, extrasaction='ignore')
                    dict_writer.writeheader()
                dict_writer.writerows(states)
                l += len(states)
        with open(os.path.join(dirpath, "_meta.txt"), "w") as f:
            f.write(",".join(indexes))
        logger.debug("Data for command {} is ready".format(cmd))
        julia_p.sendline('{} {}'.format(dirpath, model))
        last_line = None
        stdout = julia_p.readline().decode()
        while "Done" not in stdout:
            logger.debug("STD %s", stdout)
            last_line = stdout
            stdout = julia_p.readline().decode()
#        lines = stdout.decode().strip().splitlines()
        acceptance = eval(last_line)
        assert type(acceptance) == list
        assert len(acceptance) == len(cmd_based_dict[cmd])
        logger.debug("Acceptance: {}".format(acceptance))
        for index in range(len(acceptance)):
            i, t, j, k = cmd_based_dict[cmd][index]
            result[i][t][j][k] = Status.ACCEPTED if acceptance[index] < threshold else Status.REJECTED
    julia_p.stdin.close()
    return result


def reduce_dimension(res: List[List[str]]):
    if not res:
        return []
    final = []
    for i in range(len(res[0])):
        vals = set([r[i] for r in res])
        if len(vals) == 1:
            final.append(vals.pop())
        else:
            final.append(Status.PARTIAL)
    return final


def verify_entry(entry: DatabaseEntry,
                 model_checking) -> NewDatabaseEntry:
    all_data = []
    for oracle_fn, trace_fn in entry.fn_inconsistent_traces:
        with open(oracle_fn, 'r') as f:
            gt_data = json.load(f)
        with open(trace_fn, 'r') as f:
            test_data = json.load(f)
        all_data.append({'mu': test_data['traces'],
                         'gt': [t for t in gt_data['traces'] if t['commands']]})

    logger.info("Len all_data: %d", len(all_data))
    cmd_based_dict, result = parse_data(all_data)
    logger.debug(cmd_based_dict)
    res = model_checking(all_data,
                         cmd_based_dict,
                         result)
    assert len(res) == len(all_data)
    logger.info("Final: {}".format(res))

    pairs = []
    for i in range(len(res)):
        oracle = VerifiedEntry(entry.fn_inconsistent_traces[i][0],
                               reduce_dimension(res[i]['gt']))
        trace = VerifiedEntry(entry.fn_inconsistent_traces[i][1],
                              res[i]['mu'][0])
        pairs.append((oracle, trace))
    return NewDatabaseEntry(entry.diff, tuple(pairs))


def compute_score(entries: List[NewDatabaseEntry]) -> None:
    tp, fp, tn, fn = 0, 0, 0, 0
    for e in entries:
        for o, t in e.fn_inconsistent_traces:
            vals = set(o.verified)
            if len(vals) > 1:
                fp += 1
            else:
                v = vals.pop()
                if v != Status.ACCEPTED:
                    fp += 1
                else:
                    tn += 1
            vals = set(t.verified)
            if len(vals) > 1:
                tp += 1
            else:
                v = vals.pop()
                if v != Status.ACCEPTED:
                    tp += 1
                else:
                    fn += 1

    logger.info("TP: %d, TN: %d, FP: %d, FN: %d", tp, tn, fp, fn)
    precision = float(tp)/float(tp + fp)
    recall = float(tp)/float(tp + tn)
    f_score = 2 * precision * recall / (precision + recall)
    logger.info("Precision: %f\nRecall: %f\nF-score: %f",
                precision, recall, f_score)


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    results = []

    with open(args.database, 'r') as f:
        db = YAML().load(f)

    candidate_mutants = [DatabaseEntry.from_dict(e) for e in db['entries'] if e['inconsistent']]
    logger.info("starting with %d mutants", len(candidate_mutants))

    validated_results = []
    futures = []
    model_checking = functools.partial(check_against_model,
                                       models_dir=args.models_dir,
                                       GBDTs_path=args.GBDTs_path,
                                       ignore_cat=args.ignore_cat,
                                       separate_params=args.separate_params,
                                       threshold=args.threshold)

    with concurrent.futures.ProcessPoolExecutor(args.threads) as e:
        for i, c in enumerate(candidate_mutants):
            future = e.submit(verify_entry, c, model_checking)
            futures.append(future)

        logger.debug("submitted all candidates")
        for future in concurrent.futures.as_completed(futures):
            res = future.result()
            if res:
                validated_results.append(res)
        logger.debug("finished executing evaluating all mutants")
    
    jsn = {
        'oracle-directory': db['oracle-directory'],
        'snapshot': db['snapshot'],
        'entries': [e.to_dict() for e in validated_results]
    }
    with open(args.output, 'w') as f:
        YAML().dump(jsn, f)
    logger.info("wrote results to file")

    compute_score(validated_results)
