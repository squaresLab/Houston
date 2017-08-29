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
        'docker',
        'pexpect',
        'geopy'
    ],
    packages = [
        'houston',
        'houston.detector',
        'houston.ardu',
        'houston.ardu.copter'
    ],
    package_dir = {
        'houston': 'houston',
        'houston.detector': 'houston/detector',
        'houston.ardu': 'houston/ardu',
        'houston.ardu.copter': 'houston/ardu/copter'
    },
    entry_points = {
        'console_scripts': [ 'houstonserver = houston.server:main' ]
    }
)
