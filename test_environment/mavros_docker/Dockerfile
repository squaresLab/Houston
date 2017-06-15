FROM ros:indigo-ros-base
MAINTAINER Jam Marcos Hernandez Quiceno "jamarck96@gmail.com"

ENV ROSVERSION "indigo"

RUN mkdir -p /home/mavros

WORKDIR /home/mavros

RUN git clone https://github.com/vishnubob/wait-for-it.git


RUN apt-get update && \
    apt-get install ros-indigo-mavros -y

RUN apt-get install realpath  -y

