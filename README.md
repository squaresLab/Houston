# Houston
### Misison control tool for robotic systems


Houston is a mission control tool for robotic systems with the extended ability to generate and analyze tests. The current version of Houston focuses on [ArduCopter](http://ardupilot.org/copter/), an open-source multi-UAV controller (see ardupilot branch). The need for a tool such as Houston arises from the fact that humans are bad at creating tests, especially for robots. 


This version of Houston is specifically for [TurtleBot](http://www.turtlebot.com/) and has not yet been expanded to generate tests. It currently only performs point to point missions.

```
$ make
$ ./run.sh
% ./runner.py 3.0 1.5
```
