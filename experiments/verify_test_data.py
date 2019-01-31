import subprocess
import tempfile
import os
import json
import csv

import argparse
from ruamel.yaml import YAML

from enum import Enum

class Status:
    ACCEPTED = 'ACCEPTED'
    REJECTED = 'REJECTED'
    UNSPECIFIED = 'UNSPECIFIED'


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Validate test traces')
    parser.add_argument('test_database', type=str, action='store',
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
    parser.add_argument('--output_file', action='store', type=str,
                        default='test_res.json',
                        help='the file where the results will be stored')
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
    julia_command = 'julia ' + str(os.path.join(GBDTs_path, 'test.jl')) + ' {} {}'
    for cmd in cmd_based_dict.keys():
        model = os.path.join(models_dir, "{}.jld".format(cmd[len('factory.'):]))
        if not os.path.isfile(model):
            print("Model doesn't exist for command {}".format(cmd))
            continue
        dirpath = tempfile.mkdtemp()
        print("tempdir: {}".format(dirpath))
        indexes = []
        l = 1
        keys = []
        dict_writer = None
        with open(os.path.join(dirpath, "data.csv.gz"), "w") as output_file:
            for i, t, j, k in cmd_based_dict[cmd]:
                print("{} {} {} {}".format(i, t, j, k))
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
        print("Data for command {} is ready".format(cmd))
        jc = julia_command.format(dirpath, model)
        julia_result = subprocess.check_output(jc, shell=True).decode().strip()
        lines = julia_result.splitlines()
        acceptance = eval(lines[-1])
        assert type(acceptance) == list
        assert len(acceptance) == len(cmd_based_dict[cmd])
        print("Acceptance: {}".format(acceptance))
        for index in range(len(acceptance)):
            i, t, j, k = cmd_based_dict[cmd][index]
            result[i][t][j][k] = Status.ACCEPTED if acceptance[index] < threshold else Status.REJECTED
    return result


def write_result(result, output_file):
    with open(output_file, 'w') as f:
        YAML().dump(result, f)

if __name__=="__main__":
    args = setup_arg_parser()
    entries = None
    results = []
    with open(args.test_database, 'r') as f:
        entries = YAML().load(f)

    all_data = []
    for e in entries['entries']:
        test_data = None
        with open(e['trace'], 'r') as f:
            test_data = json.load(f)
        gt_data = None
        with open(e['oracle'], 'r') as f:
            gt_data = json.load(f)
        all_data.append({'mu': test_data['traces'],
                         'gt': gt_data['traces']})
    print("Len all_data: %d", len(all_data))
    cmd_based_dict, result = parse_data(all_data)
    print(cmd_based_dict)
    res = check_against_model(all_data, cmd_based_dict, result, args.models_dir, args.GBDTs_path, args.ignore_cat, args.separate_params, args.threshold)
    assert len(res) == len(entries['entries'])
    print("Final: {}".format(res))

    for i in range(len(res)):
        e = entries['entries'][i]
        results.append({'diff': e['diff'],
                        'trace': e['trace'],
                        'oracle': e['oracle'],
                        'gt': res[i]['gt'],
                        'mu': res[i]['mu']})

    write_result(results, args.output_file)
