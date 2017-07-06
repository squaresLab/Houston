

from system            import System, SystemVariable, ActionSchema, Predicate, \
                              Invariant, Postcondition, Precondition, Parameter

class TurtleBot(System):

    def __init__(self):
        variables = {}
        rospy.init_node('TurtleBot')
        variables['time'] = SystemVariable('time', lambda: time.time())
        variables['x'] = SystemVariable('x',
            lambda: rospy.client.wait_for_message('/odom/', Odometry,
            timeout=1.0)).pose.pose.position.x
        variables['y'] = SystemVariable('y',
            lambda: rospy.client.wait_for_message('/odom/', Odometry,
            timeout=1.0)).pose.pose.position.y
