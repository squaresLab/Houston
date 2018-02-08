# Houston

[![Build Status](https://travis-ci.org/squaresLab/Houston.svg?branch=master)](https://travis-ci.org/squaresLab/Houston)

Awesome automated integration-test generation for robotic systems.


## Getting Started

```
$ pip install . --upgrade
```

### Executing a test case

```
import houston
import bugzoo

# we use BugZoo to provide an executable snapshot for the system under test
bz = bugzoo.BugZoo()
snapshot = bz.bugs['ardu:X']

# we produce a description of the system under test
sut = houston.ardu.ArduRover(snapshot)

# we generate a test case
# ...

# we
# ...
```
