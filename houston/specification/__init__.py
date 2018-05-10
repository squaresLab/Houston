import attrib
from pymavlink.mavutil import mavlink

__all__ = ['ReturnToLaunch']


class System(object):
    pass


class Command(object):
    pass


class MAVLinkDriver(MessageDriver):
    pass


class MAVLinkCommand(Command):
    pass

    # TODO messages should be typed
    def dispatch(self,
                 sut: System,  # FIXME this is awful
                 ) -> None:
        # construct the message
        # 
        # 7 params

        # TODO block


# MessageFormat: convert command to a message
# - wait for acknowledgement


class MAVLinkConnection(Connection):
    # how do we get the state of the system?
    def __init__(self, ) -> None:
        cool

        # router? how do we deal with messages?

    def send(self, msg: MAVLinkMessage) -> None:
        msg = \
            vehicle.message_factory.command_long_encode(0, 0, cmd_id, 0, 0, 0, 0, 0, 0, 0, 0)  # noqa: pycodestyle
        vehicle.send_mavlink(msg)
        # TODO block until finished
        pass


@attr.s
class MAVLinkMessage(Message):
    target_system = attr.ib(type=int, default=0)
    target_component = attr.ib(type=int, default=0)
    cmd_id = attr.ib(type=int)
    confirmation = attr.ib(type=int, default=0)
    param_1 = attr.ib(type=float, default=0.0)
    param_2 = attr.ib(type=float, default=0.0)
    param_3 = attr.ib(type=float, default=0.0)
    param_4 = attr.ib(type=float, default=0.0)
    param_5 = attr.ib(type=float, default=0.0)
    param_6 = attr.ib(type=float, default=0.0)
    param_7 = attr.ib(type=float, default=0.0)


class ReturnToLaunch(MAVLinkCommand):
    specification(  # ActionSpecification
        """
        :armed
        """,
        """
        (and (not :armed')
           (eq :altitude' :home_altitude)
           (eq :longitude' :home_longitude)
           (eq :latitude' :home_latitude))
        """,
        """
        (let* ([time_per_metre 3.0]
               [constant_timeout_offset 2.0]
               [distance (great_circle :altitude :longitude :latitude $altitude $longitude $latitude)]
               [time_goto (product distance time_per_metre]
               [time_land (product :altitude time_per_metre])
            (sum time_goto time_land constant_timeout_offset)
        )
        """)

    def to_message(self) -> MAVLinkMessage:
        return MAVLinkMessage(cmd_id=mavlink.MAV_CMD_NAV_RETURN_TO_LAUNCH)
