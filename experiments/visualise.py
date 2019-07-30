#!/usr/bin/env python3
import argparse

import numpy as np
import matplotlib.pyplot as plt

from compare_traces import load_file as load_trace_from_file
from compare_traces import simplify_trace


COLOURS = [
    '#e6194b',
    '#3cb44b',
    '#ffe119',
    '#4363d8',
    '#f58231',
    '#911eb4',
    '#46f0f0',
    '#f032e6',
    '#bcf60c',
    '#fabebe',
    '#008080',
    '#e6beff',
    '#9a6324',
    '#fffac8',
    '#800000',
    '#aaffc3',
    '#808000',
    '#ffd8b1',
    '#000075',
    '#808080',
    '#ffffff',
    '#000000'
]


def parse_args():
    p = argparse.ArgumentParser(description='visualises trace files.')
    p.add_argument('files', nargs='+',
                   help='path to trace file.')
    p.add_argument('--vars', type=str, default=None,
                   help='comma-delimited list of variables to plot.')
    p.add_argument('--simple', action='store_true',
                   help='plots simplified traces.')
    p.add_argument('--save', action='store', default='',
                   help="save to file")
    return p.parse_args()


def get_detailed_plot_data(var_name, mission_trace):
    x = []
    y = []
    #for command_trace in mission_trace.commands:
    command_trace = mission_trace.commands[7]
    for state in command_trace.states:
        x.append(state.time_offset)
        y.append(state[var_name])
    return x, y


def get_simple_plot_data(var_name, mission_trace):
    x = []
    y = []
    for i, state in enumerate(simplify_trace(mission_trace)):
        x.append(i)
        y.append(state[var_name])
    return x, y


def plot_var(v, idx, num_subplots, coloured_traces, func_trace_to_plot_data):
    plt.subplot(num_subplots, 1, idx)
    for i, (colour, mission_trace) in enumerate(coloured_traces):
        x, y = func_trace_to_plot_data(v, mission_trace)
        plt.plot(x, y, color=colour)
    plt.title(v)


def plot(variables, coloured_traces, simple=True, save=''):
    num_vars = len(variables)
    converter = get_simple_plot_data if simple else get_detailed_plot_data
    for i, var_name in enumerate(variables):
        plot_var(var_name, i + 1, num_vars, coloured_traces, converter)
    if not save:
        plt.show()
    else:
        plt.savefig(save)


def main():
    args = parse_args()

    # use different colours for different trace files
    coloured_traces = []
    for i, fn in enumerate(args.files):
        colour = COLOURS[i]
        mission, traces = load_trace_from_file(fn)
#        coloured_traces += [(colour, t) for t in traces]
        for t in traces:
            if t.commands:
                coloured_traces.append((colour, t))
                break

    if args.vars:
        variables = [v.strip() for v in args.vars.split(',')]
    else:
        variables = [
            'armed',
            'armable',
            'altitude',
            'home_longitude',
            'home_latitude',
            'longitude',
            'latitude',
            'vx',
            'vy',
            'vz',
            'airspeed',
            'pitch',
            'yaw',
            'roll',
            'heading',
            'groundspeed',
            'ekf_ok',
#            'throttle_channel',
#            'roll_channel'
        ]
    variables.sort()

    plot(variables, coloured_traces, simple=args.simple, save=args.save)


if __name__ == '__main__':
    main()
