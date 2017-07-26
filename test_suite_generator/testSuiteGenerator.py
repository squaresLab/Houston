import randomTestSuiteGenerator

TEMP_FORMAT = {
    'goto':{
        'altitude': float,
        'latitude': float,
        'longitude': float
    },
    'takeoff':{
        'altitude': float
    },
    'setmode': {
        'mode': str
    },
    'land':{},
    'arm':{}
}
MAX_MISSIONS = 30
MAX_ACTIONS = 20


def main():
    randomTestSuiteGenerator2 = randomTestSuiteGenerator.RandomTestSuiteGenerator()
    randomTestSuiteGenerator2.generateRandomTestSuite(TEMP_FORMAT, MAX_MISSIONS,
        MAX_ACTIONS)

if __name__ == '__main__':
    main()
