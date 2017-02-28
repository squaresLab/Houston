FROM christimperley/turtlebot:source

RUN apt-get update && \
    apt-get install -y vim

ADD test.sh /catkin_ws
ADD robotest.launch /catkin_ws/src/turtlebot_simulator/turtlebot_gazebo/launch
RUN sed -i "s#includes/amcl.launch.xml#includes/amcl/amcl.launch.xml#" \
    /catkin_ws/src/turtlebot_simulator/turtlebot_gazebo/launch/amcl_demo.launch
ADD runner.py /catkin_ws/runner.py
