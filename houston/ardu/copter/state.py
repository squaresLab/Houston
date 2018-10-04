__all__ = ['State']

from ...state import State as BaseState
from ...state import var


class State(BaseState):
    home_latitude = var(float, lambda c: -35.362938)  # TODO: fixed
    home_longitude = var(float, lambda c: 149.165085)  # TODO: fixed
    altitude = var(float,
                   lambda c: c.connection.location.global_relative_frame.alt,  # noqa: pycodestyle
                   noise=0.05)
    latitude = var(float,
                   lambda c: c.connection.location.global_relative_frame.lat,  # noqa: pycodestyle
                   noise=0.0005)
    longitude = var(float,
                    lambda c: c.connection.location.global_relative_frame.lon,  # noqa: pycodestyle
                    noise=0.0005)
    armable = var(bool, lambda c: c.connection.is_armable)
    armed = var(bool, lambda c: c.connection.armed)
    mode = var(str, lambda c: c.connection.mode.name)
    vx = var(float, lambda c: c.connection.velocity[0], noise=0.05)
    vy = var(float, lambda c: c.connection.velocity[1], noise=0.05)
    vz = var(float, lambda c: c.connection.velocity[2], noise=0.05)
    pitch = var(float, lambda c: c.connection.attitude.pitch, noise=0.05)
    yaw = var(float, lambda c: c.connection.attitude.yaw, noise=0.05)
    roll = var(float, lambda c: c.connection.attitude.roll, noise=0.05)
    heading = var(float, lambda c: c.connection.heading, noise=2)
    airspeed = var(float, lambda c: c.connection.airspeed, noise=0.05)
    groundspeed = var(float, lambda c: c.connection.groundspeed, noise=0.05)
    ekf_ok = var(bool, lambda c: c.connection.ekf_ok)
    throttle_channel = var(float, lambda c: c.connection.channels['3'])
    roll_channel = var(float, lambda c: c.connection.channels['1'])
