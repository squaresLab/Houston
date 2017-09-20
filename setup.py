#!/usr/bin/python2.7
from setuptools import setup

setup(
    name='houston',
    version='0.1.0',
    description='TBA',
    long_description='TBA',
    # need to modify to have multiple authors!
    author='Chris Timperley, Jam M. Hernandez Q.',
    author_email='christimperley@gmail.com, jamarck96@gmail.com',
    url='https://github.com/ChrisTimperley/Houston',
    license='mit',
    #dependency_links=['https://hg.python.org/cpython/raw-file/2.7/Lib/xmlrpclib.py#egg=xmlrpclib-2.7'],
    install_requires = [
        'flask',
        # 'docker',
        # 'pathos', (this is a dependency of the experiment)
        'pexpect',
        'geopy'
    ],
    packages = [
        'houston',
        'houston.generator',
        'houston.ardu',
        'houston.ardu.copter',
        'houston.ardu.rover'
    ],
    package_dir = {
        'houston': 'houston',
        'houston.generator': 'houston/generator',
        'houston.ardu': 'houston/ardu',
        'houston.ardu.copter': 'houston/ardu/copter',
        'houston.ardu.rover': 'houston/ardu/rover'
    },
    entry_points = {
        'console_scripts': [ 'houstonserver = houston.server:main' ]
    }
)
