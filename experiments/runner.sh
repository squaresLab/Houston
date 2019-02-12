#!/bin/bash

COMMANDS=("MAV_CMD_NAV_WAYPOINT"  "MAV_CMD_NAV_TAKEOFF"  "MAV_CMD_NAV_LOITER_UNLIM"  "MAV_CMD_NAV_LOITER_TURNS"  "MAV_CMD_NAV_LOITER_TIME"  "MAV_CMD_NAV_RETURN_TO_LAUNCH"  "MAV_CMD_NAV_LAND" "MAV_CMD_NAV_SPLINE_WAYPOINT" "MAV_CMD_NAV_GUIDED_ENABLE" "MAV_CMD_DO_CHANGE_SPEED" "MAV_CMD_DO_SET_HOME" "MAV_CMD_DO_PARACHUTE")
DIRECTORY=$1
TRAIN_TRACES="$1/train-traces/"
PREPROCESS_DIR="$1/preprocessed/"
CLUSTERS_DIR="$1/clusters/"
GBDTSDATA_DIR="$1/GBDTs-data/"
MODELS_DIR="$1/models/"

if [ ! -d $TRAIN_TRACES ]; then
    echo "Trace directory $TRAIN_TRACES does not exist."
    exit 1
fi

preprocess () {
    if [ -d $PREPROCESS_DIR ]; then
        rm -r $PREPROCESS_DIR
    fi
    mkdir $PREPROCESS_DIR
    python experiments/preprocess_data.py $TRAIN_TRACES --output-dir $PREPROCESS_DIR
}

cluster () {
    if [ ! -d $PREPROCESS_DIR ]; then
        echo "Preprocess data before clustering"
        exit 1
    fi
    if [ -d $CLUSTERS_DIR ]; then
        rm -r $CLUSTERS_DIR
    fi
    mkdir $CLUSTERS_DIR
    for cmd in ${COMMANDS[*]}; do
        echo "Clustering for command $cmd"
        Rscript --vanilla experiments/clustering.R --data_dir $PREPROCESS_DIR -c $cmd --output_dir $CLUSTERS_DIR -n 20 -k 3 --select_best_k --list_of_vars time_offset,home_latitude,home_longitude,altitude,latitude,longitude,armable,armed,mode,vx,vy,vz,pitch,yaw,roll,heading,airspeed,groundspeed,ekf_ok,throttle_channel,roll_channel & 
    done
    wait
}

postprocess () {
    if [ ! -d $PREPROCESS_DIR ]; then
        echo "Preprocessed data is required"
        exit 1
    fi
    if [ ! -d $CLUSTERS_DIR ]; then
        echo "Clusters are required"
        exit 1
    fi
    if [ -d $GBDTSDATA_DIR ]; then
        rm -r $GBDTSDATA_DIR
    fi
    mkdir $GBDTSDATA_DIR
    for cmd in ${COMMANDS[*]}; do
        echo "Posprocessing $cmd"
        outdir=$GBDTSDATA_DIR$cmd
        mkdir $outdir
        python experiments/postprocess_data.py $CLUSTERS_DIR${cmd}_files.txt --output-dir $outdir --verbose &
    done
    wait
}

learn () {
    if [ ! -d $GBDTSDATA_DIR ]; then
        echo "GBDTs data is required"
        exit 1
    fi
    if [ -d $MODELS_DIR ]; then
        rm -r $MODELS_DIR
    fi
    mkdir $MODELS_DIR
    for cmd in ${COMMANDS[*]}; do
        echo "learning model for command $cmd depth $1"
        julia /home/afsoona/GBDTs.jl/learn.jl $GBDTSDATA_DIR$cmd --fuzzy --output_dir $MODELS_DIR --name $cmd $1 &
    done
    wait
}

testing () {
    echo "$1 $2"
}

"${@:2}"
