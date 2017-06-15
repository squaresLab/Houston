# Houston
### Misison control tool for robotic systems


Houston can be described as a mission control tool for robotic systems with the extended functionalities of generating and analyzing tests. The current version of Houston focuses on [ArduCopter](http://ardupilot.org/copter/) an open-source multi UAV controller (see ardupilot branch). The need for a tool such as Houston arises when contemplating how bad humans are at creating tests, specially for robots. 

This version of Houston is specifically for [TurtleBot](http://www.turtlebot.com/) and has not yet implemented with a test generator. It currently only performs point to point missions.

```
$ make
$ ./run.sh
% ./runner.py 3.0 1.5
```
