import subprocess
import logging
import os
import json
import csv

import argparse


logger = logging.getLogger('houston')  # type: logging.Logger
logger.setLevel(logging.DEBUG)


def setup_logging(verbose: bool = False) -> None:
    log_to_stdout = logging.StreamHandler()
    log_to_stdout.setLevel(logging.DEBUG if verbose else logging.INFO)
    logging.getLogger('houston').addHandler(log_to_stdout)
    logging.getLogger('experiment').addHandler(log_to_stdout)


def setup_arg_parser():
    parser = argparse.ArgumentParser(description='Posprocess data')
    parser.add_argument('files', type=str, action='store',
                       help='txt file containing ordered list of files to process.')
    parser.add_argument('--output-dir', action='store', type=str,
                        default='GBDT-data/',
                        help='the directory where the results will be stored')
    parser.add_argument('--verbose', action='store_true',
                        default=False,
                        help='run in verbose mode')
    args = parser.parse_args()
    return args


def transform_data(files_filename, output_dir):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    data_filename = os.path.join(output_dir, 'data.csv.gz')
    meta_filename = os.path.join(output_dir, '_meta.txt')
    files = []
    with open(files_filename, 'r') as f:
        for row in f:
            if row.strip():
                files.append(row.strip())
    logger.debug("Total number of %d files", len(files))

    heads = []
    index = 1
    for filename in files:
        result = subprocess.check_output("wc -l {}".format(filename), shell=True).decode().strip()
        linecount = int(result.split(' ')[0])
        heads.append(str(index))
        if index == 1:
            os.system("cp {} {}".format(filename, data_filename))
        else:
            os.system("tail -n {} {} >> {}".format(linecount-1, filename, data_filename))
        index += linecount - 1
        if len(heads) % 10 == 0:
            logger.debug("%d done", len(heads))

    assert len(heads) == len(files)
    logger.debug("writing the meta file")
    with open(meta_filename, 'w') as f:
        f.write(",".join(heads))
    logger.debug("meta file written")

    #TODO remove this
    labels_file = os.path.basename(files_filename)[:-1*len("files.txt")] + "labels.txt"
    labels_file = os.path.join(os.path.dirname(files_filename), labels_file)
    os.system("cp {} {}".format(labels_file, os.path.join(output_dir, "labels.txt")))

if __name__=="__main__":
    args = setup_arg_parser()
    setup_logging(args.verbose)
    transform_data(args.files, args.output_dir)
