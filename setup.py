#!/usr/bin/python2.7
from setuptools import setup

setup(
    name='houston',
    version='0.0.1',
    description='TBA',
    long_description='TBA',
    # need to modify to have multiple authors!
    author='Chris Timperley, Jam M. Hernandez Q.',
    author_email='christimperley@gmail.com, jamarck96@gmail.com',
    url='https://github.com/ChrisTimperley/Houston',
    license='mit',
    #dependency_links=['https://hg.python.org/cpython/raw-file/2.7/Lib/xmlrpclib.py#egg=xmlrpclib-2.7'],
    install_required=['flask'],
    packages=['houston'],
    entry_points = {
        'console_scripts': [ 'houstonserver = houston.server:main' ]
    }
)
