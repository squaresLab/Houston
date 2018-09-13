__all__ = ['Configuration']

from ..configuration import Configuration as BaseConfiguration
from ..configuration import option


class Configuration(BaseConfiguration):
    speedup = option(int)
    min_parachute_alt = option(float)
