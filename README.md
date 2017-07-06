<<<<<<< HEAD
# Houston
### Misison control tool for robotic systems


Houston is a mission control tool for robotic systems with the extended ability to generate and analyze tests. The current version of Houston focuses on [ArduCopter](http://ardupilot.org/copter/), an open-source multi-UAV controller (see ardupilot branch). The need for a tool such as Houston arises from the fact that humans are bad at creating tests, especially for robots. 


This version of Houston is specifically for [TurtleBot](http://www.turtlebot.com/) and has not yet been expanded to generate tests. It currently only performs point to point missions.
=======
# Houston (ArduCopter Version)
Houston is a mission control tool for robotic systems with the extended ability to generate and analyze tests. This version of Houston focuses on [ArduCopter](http://ardupilot.org/copter/), an open-source multi-UAV controller. The need for a tool such as Houston arises from the fact that humans are bad at creating tests, especially for robots.
>>>>>>> ardupilot

Houston supports our main goal to automatically generate high-quality test suites for robotic systems. Houston uses [ROS](http://www.ros.org/about-ros/), a framework for developing robotic applicaitons. In the case of ArduCopter, Houston works directly with [MAVROS](http://wiki.ros.org/mavros) which works as a proxy for ground control.
## 1. Mission parameters
Mission parameters are a set of values that represent the expected behavior of a system. Such values can change depending in the mission type. Houston can receive as input a JSON file containing mission specifications such as the following:
* Quality attributes
* Intents
* Failure flags
* Actions (steps to accomplish a goal)

Examples of JSON files can be seen in the mission_examples directory.

### 1.1 Quality Attributes
Having data available regarding the performance of the system allows us to understand the system and its mission performance. It can also provide us with needed data for the development of automatic semi-directed test generation. Example of quality attributes are the following:
* Time
* Power consumption
* Max height
* Min height
* Distance traveled (TODO)

Quality attributes are reported every given time frame, meaning that we have to pass a *ReportRate* value in quality attributes

### 1.2 Intents
Intents are expectations for the system under test. Intents can vary depending on the given mission. They can also bound a mission. For example, if a given system exceeds a marked height, the final report masks such an event as a "unmet intent"
* Finish an action in a given time frame
* Finish using less than a percentage of battery
* Boundaries in height (post takeoff and previous to land)

### 1.3 Failure Failure Flags
As with intents, failure flags bound a mission, with the difference that if such "intent" is unmet, the mission stops and immediately marks the test as failed.

### 1.4 Missions
We now present three missions. We use JSON files to pass all the mission information to Houston which executes and monitors the mission.  
* **Point to point (PTP)**:
  Commands the system to start a given location then move to another position.
* **Multiple point to point(MPTP)**:
  Commands the system to visit multiple locations.
* **Extraction**:
  Commands the system to visit a given location, lands, waits a set amount of time, then returns to its starting position.

## 2. Test Environment
In the specific case of ArduPilot, Houston requires the following programs to be running:
* ArduCopter
* Gazebo
* ROS (roscore)
* MAVROS (ground control node)

Note that Gazebo is not a necessity, but it does help visualize the test. It can also add more variation to the tests by providing different maps (worlds).

### 2.1 Setting up the Testing Environment
We use docker [containers](https://www.docker.com/what-docker) to facilitate the test environment setup.
* **Gazebo**: Running gazebo on a docker container can be difficult since there are multiple dependency issues. We have decided to run Gazebo in the non-simulated computer. A tested version of Gazebo for this setup can be found [here](https://github.com/osrf/uctf/tree/master/doc/install_binary). For more information visit the ArduPilot gazebo installation guide [here](http://ardupilot.org/dev/docs/using-gazebo-simulator-with-sitl.html)


## Running Houston
To simplify the test environment we use [docker-compose](https://docs.docker.com/compose/) for roscore, mavros, and ardupilot.

  * **Docker-compose**:
  ```
  cd test_environment
  docker-compose up
  ```
  * **Gazebo terminal** (Assuming you have installed the version that we tested):
  ```
  cd /opt/sasc/share/gazebo-8/
  export INSTALL_SPACE=/opt/sasc
  . ${INSTALL_SPACE}/setup.bash
  . ${INSTALL_SPACE}/share/gazebo-8/setup.sh
  . ${INSTALL_SPACE}/share/uctf/setup.sh
  export GAZEBO_MODEL_PATH=$GAZEBO_MODEL_PATH:${INSTALL_SPACE}/share/gazebo_models
  export PATH=/opt/sasc/bin:$PATH
  gazebo worlds/iris_arducopter_demo.world
  ```
  * **Houston** (cool part):
  As an example we are just going to run a PTP mission.
  ```
  python runner.py random-mission PTP 1
  ```
  Hopefully you can see the magic happen.
