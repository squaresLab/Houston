__all__ = ('HomeLocation',)

from typing import Dict, Any

import attr


@attr.s(frozen=True)
class HomeLocation:
    latitude = attr.ib(type=float)
    longitude = attr.ib(type=float)
    altitude = attr.ib(type=int)
    heading = attr.ib(type=int)

    def __str__(self) -> str:
        return "{},{},{},{}".format(self.latitude,
                                    self.longitude,
                                    self.altitude,
                                    self.heading)

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'HomeLocation':
        return HomeLocation(**d)

    def to_dict(self) -> Dict[str, Any]:
        return {'latitude': self.latitude,
                'longitude': self.longitude,
                'altitude': self.altitude,
                'heading': self.heading}
