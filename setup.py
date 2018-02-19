from setuptools import setup

setup(
    name='houston',
    version='0.1.0',
    description='TBA',
    long_description='TBA',
    # need to modify to have multiple authors!
    author='Chris Timperley, Jam M. Hernandez Q., Afsoon Afzal',
    author_email='christimperley@gmail.com, jamarck96@gmail.com, afsoona@cs.cmu.edu',
    url='https://github.com/squaresLab/Houston',
    license='mit',
    python_requires='>=3.5',
    install_requires = [
        'flask',
        # 'docker',
        # 'pathos', (this is a dependency of the experiment)
        'pexpect',
        'geopy',
        'bugzoo',
        'dronekit'
    ],
    packages = [
        'houston',
        'houston.generator',
        'houston.ardu',
        'houston.ardu.common',
        'houston.ardu.copter',
        'houston.ardu.rover'
    ],
    package_dir = {
        'houston': 'houston',
        'houston.generator': 'houston/generator',
        'houston.ardu': 'houston/ardu',
        'houston.ardu.common': 'houston/ardu/common',
        'houston.ardu.copter': 'houston/ardu/copter',
        'houston.ardu.rover': 'houston/ardu/rover'
    },
    entry_points = {
        'console_scripts': [ 'houstonserver = houston.server:main' ]
    }
)
