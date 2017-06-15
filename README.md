# Houston (ArduCopter Version)
Houston is a mission control tool for robotic systems with the extended ability to generate and analyze tests. This version of Houston focuses on [ArduCopter](http://ardupilot.org/copter/), an open-source multi-UAV controller. The need for a tool such as Houston arises from the fact that humans are bad at creating tests, especially for robots.

Houston supports our main goal to automatically generate high-quality test suites for robotic systems. Houston uses [ROS](http://www.ros.org/about-ros/), a framework for developing robotic applicaitons. In the case of ArduCopter, Houston works directly with [MAVROS](http://wiki.ros.org/mavros) which works as a proxy for ground control.

### 1. Mission parameters
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
