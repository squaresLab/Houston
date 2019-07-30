import os
import json
import csv
import yaml
import logging
import random

import argparse
from ruamel.yaml import YAML

from ground_truth import DatabaseEntry
from filter_truth import filter_truth_traces, VALID_LIST_OUTPUT

logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)



state_vars = [
        {'name': 'home_latitude',
            'type': 'float',
            'flags': ''
            },
        {'name': 'home_longitude',
            'type': 'float',
            'flags': ''
            },
        {'name': 'altitude',
            'type': 'float',
            'flags': ''
            },
        {'name': 'latitude',
            'type': 'float',
            'flags': ''
            },
        {'name': 'longitude',
            'type': 'float',
            'flags': ''
            },
        {'name': 'armable',
            'type': 'boolean',
            'flags': ''
            },
        {'name': 'armed',
            'type': 'boolean',
            'flags': ''
            },
        {'name': 'mode',
            'type': 'java.lang.String',
            'flags': 'is_enum'
            },
        {'name': 'vx',
            'type': 'float',
            'flags': ''
            },
        {'name': 'vy',
            'type': 'float',
            'flags': ''
            },
        {'name': 'vz',
            'type': 'float',
            'flags': ''
            },
        {'name': 'pitch',
            'type': 'float',
            'flags': ''
            },
        {'name': 'yaw',
            'type': 'float',
            'flags': ''
            },
        {'name': 'roll',
            'type': 'float',
            'flags': ''
            },
        {'name': 'heading',
            'type': 'float',
            'flags': ''
            },
        {'name': 'airspeed',
            'type': 'float',
            'flags': ''
            },
        {'name': 'groundspeed',
            'type': 'float',
            'flags': ''
            },
        {'name': 'ekf_ok',
            'type': 'boolean',
            'flags': ''
            },
#        {'name': 'throttle_channel',
#            'type': 'float',
#            'flags': ''
#            },
#        {'name': 'roll_channel',
#            'type': 'float',
#            'flags': ''
#            }
]

def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Preprocess traces')
    parser.add_argument('traces', type=str, action='store',
                       help='path to trace files.')
    parser.add_argument('commands', type=str, action='store',
                        help='commands yamle file')
    parser.add_argument('output', action='store', type=str,
                        help='the directory where the results will be stored')
    parser.add_argument('--database', action='store', type=str,
                        default='',
                        help='path to database yaml file')
    parser.add_argument('--ground-truth', action='store', type=str,
                        default='',
                        help='path to ground truth data')
    parser.add_argument('--verbose', action='store_true',
                        default=False,
                        help='run in verbose mode')
    parser.add_argument('--seed', action='store', type=int,
                        default=1,
                        help='random seed')
    parser.add_argument('--percentage', action='store', type=float,
                        default=1.0,
                        help='percentage of data to consider')
    args = parser.parse_args()
    return args


def create_trace_file(traces, output_filename):
    ppt_val = """
{name}:::{sub}
this_invocation_nonce
{nonce}
"""
    var_val = """{name}
{val}
1
"""
    with open(output_filename, 'w') as f:
        pass

    index = 1
    fn_to_nonce = {}
    for filename in traces:
        with open(filename, 'r') as f:
            j = json.load(f)
        traces = [t for t in j['traces'] if t['commands']]
        nonces = []
        for c in traces[0]['commands']:
            nonce = str(index)
            parameters = ''
            for name in sorted(c['command']['parameters']):
                parameters += var_val.format(name='p_{}'.format(name), val=c['command']['parameters'][name])
            state_b = c['states'][0]
            state_e = c['states'][-1]
            states = ''
            for s in state_vars:
                name = s['name']
                val = state_b[name]
                if type(val) == bool:
                    val = int(val)
                elif type(val) == str:
                    val = '"{}"'.format(val)
                states += var_val.format(name=name, val=val)
            with open(output_filename, 'a') as f:
                f.write(ppt_val.format(name=c['command']['type'], sub='ENTER', nonce=nonce))
                f.write(parameters)
                f.write(states)
            states = ''
            for s in state_vars:
                name = s['name']
                val = state_e[name]
                if type(val) == bool:
                    val = int(val)
                elif type(val) == str:
                    val = '"{}"'.format(val)
                states += var_val.format(name=name, val=val)
            with open(output_filename, 'a') as f:
                f.write(ppt_val.format(name=c['command']['type'], sub='EXIT0', nonce=nonce))
                f.write(parameters)
                f.write(states)
            
            nonces.append(int(nonce))
            index += 1
        fn_to_nonce[filename] = nonces

    with open(output_filename +  '_nonce.yml', "w") as f:
        YAML().dump(fn_to_nonce, f)



def create_decl_file(command_yml_filename, output_filename):
    topping = """decl-version 2.0
input-language houston
var-comparability implicit
"""
    var_decl = """variable {name}
  var-kind variable
  dec-type {type}
  rep-type {type}
  flags not_ordered {flags}
  comparability 22
"""
    ppt_decl = """
ppt {name}:::{sub}
ppt-type {type}
"""
    
    states = ''
    for s in state_vars:
        states += var_decl.format(**s)
    with open(command_yml_filename, 'r') as f:
        all_commands = yaml.load(f)['commands']

    with open(output_filename, 'w') as f:
        f.write(topping)

    for c in all_commands:
        params = []
        for i in range(1, 8):
            p = 'p{}'.format(i)
            if p in c:
                param = None
                p_name = 'p_{}'.format(c[p]['name'])
                typ = c[p]['value']['type']
                if typ == 'discrete':
                    p_dic = {'name': p_name,
                            'type': 'int',
                            'flags': 'is_enum nomod'
                        }
                elif typ == 'continuous':
                    p_dic = {'name': p_name,
                            'type': 'float',
                            'flags': 'nomod'
                            }
                params.append(p_dic)
        params = sorted(params, key=lambda a: a['name'])
        params = [var_decl.format(**p) for p in params]
        parameters = ''.join(params)
        with open(output_filename, 'a') as f:
            f.write(ppt_decl.format(name='factory.{}'.format(c['name']), sub='ENTER', type='enter'))
            f.write(parameters)
            f.write(states)
            f.write('\n')
            f.write(ppt_decl.format(name='factory.{}'.format(c['name']), sub='EXIT0', type='exit'))
            f.write(parameters)
            f.write(states)


if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    random.seed(args.seed)

    output_dir = args.output
    data_dir = args.traces
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    with open(os.path.join(data_dir, VALID_LIST_OUTPUT), 'r') as f:
        valid_truth = YAML().load(f)
    traces = [os.path.join(data_dir, v) for v in valid_truth]
    if args.percentage < 1:
        num = int(args.percentage * len(traces))
        traces = random.sample(traces, num)
        logger.debug('sampled %d traces', num)
 
    logger.debug("Preparing the declaration file")
    #create_decl_file(args.commands, os.path.join(output_dir, 'ardu.decls'))
    logger.debug("Preparing training data dtrace file")
    #create_trace_file(traces, os.path.join(output_dir, 'ardu.dtrace'))

    if args.database:
        with open(args.database, 'r') as f:
            db = YAML().load(f)
        with open(os.path.join(args.ground_truth, VALID_LIST_OUTPUT), 'r') as f:
            all_truth = YAML().load(f)
        all_truth = [os.path.join(args.ground_truth, t) for t in all_truth]

        entries = [t['trace'] for e in db['entries'] for t in e['inconsistent']]
        logger.info("total number of %d mutants", len(entries))

        test = entries
        test.extend(all_truth[:len(entries)])
        logger.debug("Preparing test dtrace file %d", len(test))
        create_trace_file(test, os.path.join(output_dir, 'test.dtrace'))
    logger.debug("Done")
