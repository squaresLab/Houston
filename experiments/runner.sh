#!/bin/bash

COMMANDS=("MAV_CMD_NAV_WAYPOINT"  "MAV_CMD_NAV_TAKEOFF"  "MAV_CMD_NAV_LOITER_TURNS"  "MAV_CMD_NAV_LOITER_TIME"  "MAV_CMD_NAV_RETURN_TO_LAUNCH"  "MAV_CMD_NAV_LAND"  "MAV_CMD_NAV_SPLINE_WAYPOINT"  "MAV_CMD_DO_CHANGE_SPEED"  "MAV_CMD_DO_SET_HOME"  "MAV_CMD_DO_PARACHUTE")
DIRECTORY=$1
NUMBER_OF_SEEDS=$2
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
    echo "start preprocess"
    python experiments/preprocess_data.py $TRAIN_TRACES --output-dir $PREPROCESS_DIR --threads 40
    echo "preprocess done"
}

cluster () {
    if [ ! -d $PREPROCESS_DIR ]; then
        echo "Preprocess data before clustering"
        exit 1
    fi
    if [ ! -d $CLUSTERS_DIR ]; then
        mkdir $CLUSTERS_DIR
    fi
    echo "start cluster"
    for i in $(seq 1 ${NUMBER_OF_SEEDS}); do
        CL="${CLUSTERS_DIR}seed_$i/"
        if [ -d $CL ]; then
            rm -r $CL
        fi
        mkdir $CL
        for cmd in ${COMMANDS[*]}; do
            echo "Clustering for command $cmd seed $i"
            Rscript --vanilla experiments/clustering.R --data_dir $PREPROCESS_DIR -c $cmd --output_dir $CLUSTERS_DIR -n 20 -k 3 --select_best_k --list_of_vars time_offset,home_latitude,home_longitude,altitude,latitude,longitude,armable,armed,mode,vx,vy,vz,pitch,yaw,roll,heading,airspeed,groundspeed,ekf_ok --seed $i &
        done
    done
    wait
    echo "cluster done"
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
    if [ ! -d $GBDTSDATA_DIR ]; then
        mkdir $GBDTSDATA_DIR
    fi
    echo "start postprocess"
    for i in $(seq 1 ${NUMBER_OF_SEEDS}); do
        GB="${GBDTSDATA_DIR}seed_$i/"
        if [ -d $GB ]; then
            rm -r $GB
        fi
        mkdir $GB
        for cmd in ${COMMANDS[*]}; do
            echo "Posprocessing $cmd"
            outdir=$GB$cmd
            mkdir $outdir
            python experiments/postprocess_data.py ${CLUSTERS_DIR}seed_$i/${cmd}_files.txt --output-dir $outdir --verbose &
        done
    done
    wait
    echo "postprocess done"
}

learn () {
    depth=10
    if [ ! -d $GBDTSDATA_DIR ]; then
        echo "GBDTs data is required"
        exit 1
    fi
    if [ ! -d $MODELS_DIR ]; then
        mkdir $MODELS_DIR
    fi
    echo "start learn"
    for i in $(seq 1 ${NUMBER_OF_SEEDS}); do
        MD="${MODELS_DIR}seed_$i/"
        if [ -d $MD ]; then
            rm -r $MD
        fi
        mkdir $MD
        for cmd in ${COMMANDS[*]}; do
            echo "learning model for command $cmd depth $1 seed $i"
            julia /home/afsoona/GBDTs.jl/learn.jl ${GBDTSDATA_DIR}_seed$i/$cmd --output_dir $MD --name $cmd $depth --fuzzy &
            julia /home/afsoona/GBDTs.jl/learn.jl ${GBDTSDATA_DIR}_seed$i/$cmd --output_dir $MD --name $cmd $depth &
        done
    done
    wait
    echo "learn done"
}

testing () {
    echo "Testing $TRAIN_TRACES $NUMBER_OF_SEEDS"
}

for var in "${@:3}"
do
    "$var"
done

#preprocess
#cluster
#postprocess
#learn 10

