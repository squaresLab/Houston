import subprocess
import tempfile
import os
import json
import csv

import argparse

from enum import IntEnum

class Status(IntEnum):
    ACCEPTED = 1
    REJECTED = 2
    UNSPECIFIED = 3



def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Validate test traces')
    parser.add_argument('test_data', type=str, action='store',
                       help='path to test json file.')
    parser.add_argument('models_dir', type=str, action='store',
                        help='path to directory with learned models.')
    parser.add_argument('GBDTs_path', type=str, action='store',
                        help='path to GBDTs.')
    parser.add_argument('--threshold', type=float, action='store',
                        default=0.4,
                        help='threshold for accepting a trace')
    parser.add_argument('--ignore_cat', action='store_true',
                        default=False,
                        help='ignore categorical fields of the data.')
    parser.add_argument('--output_file', action='store', type=str,
                        default='test_res.json',
                        help='the file where the results will be stored')
    args = parser.parse_args()
    return args


def parse_data(test_data):
    all_data = None
    with open(test_data, 'r') as f:
        all_data = json.load(f)
    useful_data = []
    cmd_based_dict = {}
    result = []
    for i in range(len(all_data)):
        m = all_data[i]['traces']
        result.append({'gt': [], 'mu': []})
        useful_data.append({'gt': m['ground-truth'], 'mu': m['mutant']})
        for j in range(len(m["ground-truth"])):
            trace = m["ground-truth"][j]
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
        for j in range(len(m["mutant"])):
            trace = m["mutant"][j]
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
    return useful_data, cmd_based_dict, result

def check_against_model(all_data, cmd_based_dict, result, models_dir, GBDTs_path, ignore_cat, threshold=0.4):
    julia_command = 'julia ' + str(os.path.join(GBDTs_path, 'test.jl')) + ' {} {}'
    for cmd in cmd_based_dict.keys():
        model = os.path.join(models_dir, "{}.jld".format(cmd))
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
                if not dict_writer:
                    if not ignore_cat:
                        keys = list(c['states'][0].keys())
                    else:
                        keys = [n for n in sorted(c['states'][0]) if type(c['states'][0][n]) == float]
                    dict_writer = csv.DictWriter(output_file, keys, extrasaction='ignore')
                    dict_writer.writeheader()
                dict_writer.writerows(c['states'])
                l += len(c['states'])
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
        json.dump(result, f)

if __name__=="__main__":
    args = setup_arg_parser()
    all_data, cmd_based_dict, result = parse_data(args.test_data)
    print(cmd_based_dict)
    #print(all_data)
    res = check_against_model(all_data, cmd_based_dict, result, args.models_dir, args.GBDTs_path, args.ignore_cat, args.threshold)
    print("Final: {}".format(res))
    write_result(res, args.output_file)
