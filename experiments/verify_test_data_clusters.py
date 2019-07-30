from typing import Iterator, Tuple, Set, List, Dict, Any, Optional, Type
import logging
import subprocess
import pexpect
import tempfile
import os
import json
import csv
import yaml
import attr
import functools
import time
import math
import numpy as np

import argparse
import concurrent.futures

from ruamel.yaml import YAML

from ground_truth import DatabaseEntry
from compare_traces import load_file
from hash_mutants import mutation_to_uid
from filter_truth import VALID_LIST_OUTPUT

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
    parser.add_argument('data_dir', type=str, action='store',
                        help='path to directory with cluster output.')
    parser.add_argument('ground_truth', type=str, action='store',
                        help='path to ground truth traces')
    parser.add_argument('--threshold', type=float, action='store',
                        default=0.4,
                        help='threshold for accepting a trace')
    parser.add_argument('--clusters', type=str, action='store',
                        default='',
                        help='threshold for accepting a trace')
#    parser.add_argument('output', action='store', type=str,
#                        help='the file where the results will be stored')
    parser.add_argument('--threads', type=int, default=1,
                         help='number of threads')
    parser.add_argument('--verbose', action='store_true',
                         help='increases logging verbosity.')
    parser.add_argument('--compute-score', action='store',
                        default='',
                        help='path to a csv file to add the accuracy results')

    args = parser.parse_args()
    return args


def check_against_model(trace_commands, cmd_to_res, name, threshold=0.4):

    results = [Status.UNSPECIFIED for i in range(len(trace_commands))]
    for i, cmd in enumerate(trace_commands):
        cmd_type = cmd['command']['type'][len('factory.'):]
        res = cmd_to_res[cmd_type]
        m = '{}_{}'.format(name, i)
        if m in res:
            if isinstance(threshold, float):
                if res[m] > threshold:
                    results[i] = Status.REJECTED
                else:
                    results[i] = Status.ACCEPTED
            else:
                if res[m] > threshold[cmd_type]:
                    results[i] = Status.REJECTED
                else:
                    results[i] = Status.ACCEPTED
        else:
            logger.debug("not in results %s", m)
            logger.debug("res %s", res)
            raise Exception
    return results


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


def verify_entry(entry: List[Tuple],
                 model_checking) -> NewDatabaseEntry:
    pairs = []
    for oracle_fn, trace_fn in entry:
        with open(oracle_fn, 'r') as f:
            gt_data = json.load(f)
            name = os.path.basename(oracle_fn)[:-len(".json")]
            for t in gt_data['traces']:
                if t['commands']:
                    res = model_checking(t['commands'], name=name)
                    break
            if not res:
                logger.error("WTF")
                raise Exception
            oracle = VerifiedEntry(oracle_fn, res)
        with open(trace_fn, 'r') as f:
            test_data = json.load(f)
            name = os.path.basename(trace_fn)[:-len(".json")]
            res = model_checking(test_data['traces'][0]['commands'], name=name)
            if not res:
                logger.error("WTF2")
                raise Exception
            trace = VerifiedEntry(trace_fn, res)
        pairs.append((oracle, trace))

    logger.info("Len pairs: %d", len(pairs))
    return tuple(pairs)


def compute_score(entries: List[Tuple],
                  score_file: str = '',
                  models_dir: str = '',
                  threshold: float = 0.4) -> None:
    tp, fp, tn, fn = 0, 0, 0, 0
    with open(os.path.join(models_dir, 'test-out.yml'), 'w') as f:
        for e in entries:
            for o, t in e:
                if Status.REJECTED in o.verified:
                    fp += 1
                    f.write('- {}: REJECTED\n'.format(o.fn))
                else:
                    tn += 1
                    f.write('- {}: ACCEPTED\n'.format(o.fn))
                if Status.REJECTED in t.verified:
                    tp += 1
                    f.write('- {}: REJECTED\n'.format(t.fn))
                else:
                    fn += 1
                    f.write('- {}: ACCEPTED\n'.format(t.fn))

    logger.info("TP: %d, TN: %d, FP: %d, FN: %d", tp, tn, fp, fn)
    precision = float(tp)/float(tp + fp) if tp+fp != 0 else float('nan')
    recall = float(tp)/float(tp + fn) if tp+fn != 0 else float('nan')
    f_score = (2 * tp) / (2 * tp + fp + fn) if not tp + fp + fn == 0 else float('nan')
    logger.info("Precision: %f\nRecall: %f\nF-score: %f\nAccuracy: %f",
                precision, recall, f_score, float((tp+tn)/(tp+tn+fp+fn)))
    if not score_file:
        return
    typ = 'nogbdt'
    seed = os.path.basename(models_dir)
    data_amount = '25data'
    with open(score_file, 'a') as f:
        f.write(', '.join([data_amount, seed, typ, str(threshold), str(tp), str(tn), str(fp), str(fn),
                           str(precision), str(recall), str(f_score)]))
        f.write('\n')


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    results = []

    with open(args.database, 'r') as f:
        db = YAML().load(f)
    with open(os.path.join(args.ground_truth, VALID_LIST_OUTPUT), 'r') as f:
        all_truth = YAML().load(f)
    all_truth = [os.path.join(args.ground_truth, t) for t in all_truth]

    candidate_mutants = [t['trace'] for e in db['entries'] for t in e['inconsistent']]
    fn_inconsistent_traces = list(zip(all_truth, candidate_mutants))
    logger.info("starting with %d mutants", len(candidate_mutants))
    logger.debug("total %d", len(fn_inconsistent_traces))


    cmd_to_res = {}
    quantiles = {}
    for filename in os.listdir(args.data_dir):
        if not filename.startswith('MAV'):
            continue
        with open(os.path.join(args.data_dir, filename), 'r') as f:
            res = yaml.load(f, Loader=yaml.BaseLoader)
        r = {k: float(v) for k, v in dict(res).items()}
        plain_name = filename[:-len(".yml")]
        cmd_to_res[plain_name] = r
        if args.clusters:
            with open(os.path.join(args.clusters, filename), 'r') as f:
                for l in f:
                    if l.startswith("inertia:"):
                        quantiles[plain_name] = float(l[len("inertia: "):])*args.threshold
                        break
        else:
            quantiles[plain_name] = np.percentile(list(r.values()), 90)
    logger.debug("quantiles %s", quantiles)



    validated_results = []
    futures = []
    model_checking = functools.partial(check_against_model,
                                       cmd_to_res=cmd_to_res,
#                                       threshold=args.threshold)
                                       threshold=quantiles)

    with concurrent.futures.ProcessPoolExecutor(args.threads) as e:
        i = 0
        while i < len(fn_inconsistent_traces):
            future = e.submit(verify_entry, fn_inconsistent_traces[i:i+20], model_checking)
            futures.append(future)
            i += 20

        logger.debug("submitted all candidates")
        for future in concurrent.futures.as_completed(futures):
            res = future.result()
            if res:
                validated_results.append(res)
        logger.debug("finished executing evaluating all mutants")
    
#    jsn = {
#        'oracle-directory': db['oracle-directory'],
#        'snapshot': db['snapshot'],
#        'entries': [e.to_dict() for e in validated_results]
#    }
#    with open(args.output, 'w') as f:
#        YAML().dump(jsn, f)
#    logger.info("wrote results to file")

    if args.compute_score:
        compute_score(validated_results,
                      args.compute_score,
                      args.data_dir,
                      args.threshold)
    else:
        compute_score(validated_results)
