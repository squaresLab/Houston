#!/bin/bash

COMMANDS=("MAV_CMD_NAV_WAYPOINT"  "MAV_CMD_NAV_TAKEOFF"  "MAV_CMD_NAV_LOITER_TURNS"  "MAV_CMD_NAV_LOITER_TIME"  "MAV_CMD_NAV_RETURN_TO_LAUNCH"  "MAV_CMD_NAV_LAND"  "MAV_CMD_NAV_SPLINE_WAYPOINT"  "MAV_CMD_DO_CHANGE_SPEED"  "MAV_CMD_DO_SET_HOME"  "MAV_CMD_DO_PARACHUTE")
DIRECTORY=$1
NUMBER_OF_SEEDS=$2
TRAIN_TRACES="train-traces/"
PREPROCESS_DIR="preprocessed/"
CLUSTERS_DIR="clusters/"
GBDTSDATA_DIR="GBDTs-data/"
MODELS_DIR="models/"

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
    for i in $(seq 1 ${NUMBER_OF_SEEDS}); do
        PROC=$DIRECTORY/seed_$i/$PREPROCESS_DIR
        if [ ! -d $PROC ]; then
            echo "Preprocess data before clustering $PROC"
            exit 1
        fi
        CL=$DIRECTORY/seed_$i/$CLUSTERS_DIR
        if [ -d $CL ]; then
            rm -r $CL
        fi
        echo "start cluster"
        mkdir $CL
        for cmd in ${COMMANDS[*]}; do
            if [ -f $CL${cmd}_labels.txt ]; then
                echo "Already has command $CL$cmd"
                continue
            fi
            echo "Clustering for command $cmd seed $i"
            Rscript --vanilla experiments/clustering.R --data_dir $PROC -c $cmd --output_dir $CL -n 20 -k 3 --list_of_vars time_offset,home_latitude,home_longitude,altitude,latitude,longitude,armable,armed,mode,vx,vy,vz,pitch,yaw,roll,heading,airspeed,groundspeed,ekf_ok --seed $i &
        done
    done
    wait
    echo "cluster done"
}

postprocess () {
    for i in $(seq 1 ${NUMBER_OF_SEEDS}); do
        PROC=$DIRECTORY/seed_$i/$PREPROCESS_DIR
        if [ ! -d $PROC ]; then
            echo "Preprocess data before clustering $PROC"
            exit 1
        fi
        CL=$DIRECTORY/seed_$i/$CLUSTERS_DIR
        echo "$CL"
        if [ ! -d $CL ]; then
            echo "Clusters are required"
            exit 1
        fi
        GB=$DIRECTORY/seed_$i/$GBDTSDATA_DIR
        if [ -d $GB ]; then
            rm -r $GB
        fi
        echo "start postprocess"
        mkdir $GB
        for cmd in ${COMMANDS[*]}; do
            echo "Posprocessing $cmd"
            outdir=$GB$cmd
            mkdir $outdir
            python experiments/postprocess_data.py $CL/${cmd}_files.txt --output-dir $outdir --verbose &
        done
    done
    wait
    echo "postprocess done"
}

learn () {
    depth=10
    threads=3
    if [ ! -d $GBDTSDATA_DIR ]; then
        echo "GBDTs data is required"
        exit 1
    fi
    if [ ! -d $MODELS_DIR ]; then
        mkdir $MODELS_DIR
    fi
    echo "start learn"
    for i in $(seq ${NUMBER_OF_SEEDS} ${NUMBER_OF_SEEDS}); do
        MD="${MODELS_DIR}seed_$i/"
        if [ -d $MD ]; then
            rm -r $MD
        fi
        mkdir $MD
        mkdir ${MD}fuzzy
        mkdir ${MD}normal
        for cmd in ${COMMANDS[*]}; do
            echo "learning model for command $cmd depth $depth seed $i threads $threads"
            JULIA_NUM_THREADS=$threads julia /home/afsoona/GBDTs.jl/learn.jl ${GBDTSDATA_DIR}seed_$i/$cmd --output_dir ${MD}fuzzy --name $cmd $depth --fuzzy --seed $i &
            JULIA_NUM_THREADS=$threads julia /home/afsoona/GBDTs.jl/learn.jl ${GBDTSDATA_DIR}seed_$i/$cmd --output_dir ${MD}normal --name $cmd $depth --seed $i &
        done
        wait
    done
    echo "learn done"
}

learn-noclust () {
    depth=10
    threads=3
    if [ ! -d $GBDTSDATA_DIR ]; then
        echo "GBDTs data is required"
        exit 1
    fi
    if [ ! -d $MODELS_DIR ]; then
        mkdir $MODELS_DIR
    fi
    echo "start learn"
    for i in $(seq ${NUMBER_OF_SEEDS} ${NUMBER_OF_SEEDS}); do
        MD="${MODELS_DIR}seed_$i/"
        if [ ! -d $MD ]; then
            mkdir $MD
        fi
        mkdir ${MD}noclust
        for cmd in ${COMMANDS[*]}; do
            echo "learning model for command $cmd depth $depth seed $i threads $threads"
            JULIA_NUM_THREADS=$threads julia /home/afsoona/GBDTs.jl/learn.jl ${GBDTSDATA_DIR}noclust/$cmd --output_dir ${MD}noclust --name $cmd $depth --fuzzy --seed $i &
        done
        wait
    done
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

