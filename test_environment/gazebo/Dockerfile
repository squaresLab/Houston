# http://ardupilot.org/dev/docs/using-gazebo-simulator-with-sitl.html
# https://github.com/osrf/uctf/tree/master/doc/install_binary
FROM ubuntu:16.04
MAINTAINER Jam Marcos Hernandez Quiceno "jamarck96@gmail.com"



WORKDIR /home/gazebo_ws


RUN  apt-get update && \
	apt-get -y install software-properties-common
RUN  add-apt-repository "deb http://archive.ubuntu.com/ubuntu/ $(lsb_release -sc) main universe restricted multiverse"
RUN  sh -c 'echo "deb http://packages.ros.org/ros/ubuntu $(lsb_release -sc) main" > /etc/apt/sources.list.d/ros-latest.list'



RUN apt-key adv --keyserver hkp://ha.pool.sks-keyservers.net:80 --recv-key 421C365BD9FF1F717815A3895523BAEEB01FA116
RUN  apt-key adv --keyserver hkp://ha.pool.sks-keyservers.net:80 --recv-key 0xB01FA116


RUN apt-get update && \
	apt-get install ros-kinetic-ros-base -y && \
	apt-cache search ros-kinetic && \
	rosdep init && \
	rosdep update && \
	echo "source /opt/ros/kinetic/setup.bash" >> ~/.bashrc



RUN  apt-get update && \
	 apt install python3-pyside ros-kinetic-gazebo-ros ros-kinetic-mavros ros-kinetic-opencv3 ros-kinetic-rqt ros-kinetic-xacro wget -y

RUN  sh -c 'echo "deb http://packages.osrfoundation.org/gazebo/ubuntu-stable `lsb_release -cs` main" > /etc/apt/sources.list.d/gazebo-stable.list'

RUN wget http://packages.osrfoundation.org/gazebo.key -O - |  apt-key add -

RUN  apt-get update  && \
	 apt-get install sasc-gazebo-sitl -y 

RUN apt-get install mercurial -y && \
	hg clone https://bitbucket.org/osrf/gazebo_models ~/gazebo_ws/gazebo_models

RUN cd ~/gazebo_ws/gazebo_models && \
	hg checkout zephyr_demos

RUN echo echo 'export GAZEBO_MODEL_PATH=~/gazebo_ws/gazebo_models' >> ~/.bashrc


ENV HOME "/home/gazebo_ws"
ENV PATH  "${PATH}:/opt/sasc/bin:${PATH}

ADD gazebo_entrypoint.sh /home/gazebo_ws/
CMD ". ~/.bashrc"


