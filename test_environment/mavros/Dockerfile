FROM ros:indigo-ros-base
MAINTAINER Jam Marcos Hernandez Quiceno "jamarck96@gmail.com"

ENV ROSVERSION "indigo"

RUN mkdir -p /home/mavros

WORKDIR /home/mavros


RUN apt-get update && \
    apt-get install ros-indigo-mavros -y


