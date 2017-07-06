
import actionlib
from move_base_msgs.msg import MoveBaseAction, MoveBaseGoal
from kobuki_msgs.msg    import BumperEvent
from geometry_msgs.msg import Point, Quaternion
from system            import System, SystemVariable, ActionSchema, Predicate, \
                              Invariant, Postcondition, Precondition, Parameter


class TurtleBot(System):

    def __init__(self):
        variables = {}
        rospy.init_node('TurtleBot')
        variables['time'] = InternalStateVariable('time', lambda: time.time())
        variables['x'] = InternalStateVariable('x',
            lambda: rospy.client.wait_for_message('/odom/', Odometry,
            timeout=1.0).pose.pose.position.x)
        variables['y'] = InternalStateVariable('y',
            lambda: rospy.client.wait_for_message('/odom/', Odometry,
            timeout=1.0).pose.pose.position.y)
        variables['bumper'] = InternalStateVariable('bumper',
            lambda: rospy.client.wait_for_message('/mobile_base/events/bumper/',
            BumperEvent, timeout=1.0).state == 1)


        schemas = {}
        schemas['goto'] = GoToActionSchema()

        super(TurtleBot, self).__init__(variables, schemas)


"""
A description of goto
"""
class GoToActionSchema(ActionSchema):
    def __init__(self):
        parameters = [
            Parameter('x', float, 'description'),
            Parameter('y', float, 'description')
        ]

        preconditions = []

        invariants = [
            Invariant('bumper', 'description',
                       lambda sv: sv['bumper'].read() != True)
        ]

        postconditions = [
            Postcondition('location', 'description',
                          lambda sv: euclidean(
                          (sv['x'].read(), sv['y'].read()),
                          (parameters[0].get_value, parameters[1].get_value)) < 0.3
        ]

        super(GoToActionSchema, self).__init__('goto',parameters, preconditions, invariants, postconditions)


    def dispatch(parameters):
        client = actionlib.SimpleActionClient('move_base', MoveBaseAction)
        goal = MoveBaseGoal()
        goal.target_pose.header.frame_id = "map"
        goal.target_pose.header.stamp = rospy.Time.now()
        goal.target_pose.pose.position = Point(
            parameters[0].get_value,
            parameters[1].get_value,
            1)
        goal.target_pose.pose.orientation = Quaternion(0.0, 0.0, 0.0, 1.0)
        client.send_goal(goal)

def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert len(a) != []
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)
