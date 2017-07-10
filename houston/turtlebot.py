
import actionlib
import rospy
import roslaunch
import xml.etree.ElementTree as ET
import xmlrpclib
import os
from tempfile           import NamedTemporaryFile
from move_base_msgs.msg import MoveBaseAction, MoveBaseGoal
from kobuki_msgs.msg    import BumperEvent
from geometry_msgs.msg  import Point, Quaternion
from system             import System, InternalStateVariable, ActionSchema, Predicate, \
                              Invariant, Postcondition, Precondition, Parameter, \
                              Action


class TurtleBot(System):

    def __init__(self):
        variables = {}
        
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

    def setUp(self, mission):
        launch = None

        try:
            ephemeral_launch = EphemeralLaunchFile(mission.getEnvironment().read('launch_file'), \
                mission.getEnvironment().read('launch_parameters'))
            # launch ROS
            uuid = roslaunch.rlutil.get_or_generate_uuid(None, False)
            roslaunch.configure_logging(uuid)
            launch_files = [ephemeral_launch.path()]
            launch = roslaunch.parent.ROSLaunchParent(uuid, launch_files, is_core=True)
            launch.start()
            rospy.init_node('TurtleBot')
            while not check_turtlebot_ready():
                pass
            print 'MAKING setupTRUEW'
            self.setupDone = True
            rate = rospy.Rate(10)
            
            while not rospy.is_shutdown():
                rate.sleep()
        finally:
            if launch:
                launch.shutdown()

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
                          (parameters[0].get_value, parameters[1].get_value)) < 0.3)
        ]

        super(GoToActionSchema, self).__init__('goto',parameters, preconditions, invariants, postconditions)


    def dispatch(self, parameters):
        client = actionlib.SimpleActionClient('move_base', MoveBaseAction)
        while not client.wait_for_server():
            pass
        goal = MoveBaseGoal()
        goal.target_pose.header.frame_id = "map"
        goal.target_pose.header.stamp = rospy.Time.now()
        goal.target_pose.pose.position = Point(
            float(parameters['x']),
            float(parameters['y']),
            0.0)
        goal.target_pose.pose.orientation = Quaternion(0.0, 0.0, 0.0, 1.0)
        client.send_goal(goal)

class EphemeralLaunchFile(object):

    def __init__(self, base_file, parameters):
        # load the contents of the base file
        tree = ET.ElementTree()
        tree.parse(base_file)
        root = tree.getroot()

        # find the corresponding argument for each parameter
        new_parameters = []
        for (param, value) in parameters.items():
            found = False

            # doesn't look at child arguments --- considered unnecessary
            for arg in root.find("arg[@name='{}']".format(param)):
                arg.attrib.pop('default')
                arg.set('value', value)
                found = True

            # if we didn't find the tag for this argument, add a new one
            if not found:
                arg = ET.SubElement(root, 'arg')
                arg.set('name', param)
                arg.set('value', value)

        # write the modified XML to a temporary file
        # n.b. Python will take care of destroying the temporary file during
        # garbage collection
        self.handle = NamedTemporaryFile(suffix='.launch')
        tree.write(self.path())

    def path(self):
        return self.handle.name


def euclidean(a, b):
    assert isinstance(a, tuple) and isinstance(b, tuple)
    assert len(a) != []
    assert len(a) == len(b)
    d = sum((x - y) ** 2 for (x, y) in zip(a, b))
    return math.sqrt(d)

def check_turtlebot_ready():
    m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
    code, status_message, uri = m.lookupNode('/mobile_base_nodelet_manager',\
        '/mobile_base_nodelet_manager')
    return code == 1