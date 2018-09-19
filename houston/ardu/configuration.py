__all__ = ['Configuration']

from ..configuration import Configuration as BaseConfiguration
from ..configuration import option


class Configuration(BaseConfiguration):
    speedup = option(int)
    min_parachute_alt = option(float)
    constant_timeout_offset = option(int)
    # FIXME this should be computed based on acceleration and speed
    time_per_metre_travelled = option(float)
