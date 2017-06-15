FROM ros:indigo-ros-base

RUN apt-get update && \
    apt-get install -y vim


RUN apt-get install -y ros-indigo-mavros  \
  ros-indigo-mavros-msgs                  \
  ros-indigo-mavros-extras


ADD runner.py /runner.py
