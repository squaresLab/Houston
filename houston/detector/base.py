import time
import timeit
import random
import copy
import threading
import houston.manager as mgr


from resources import ResourceUsage, ResourceLimits
from houston.system import System
from houston.branch import BranchID, BranchPath
from houston.mission import Mission, MissionOutcome
from houston.action import ActionOutcome, Action, ActionGenerator


class BugDetectorSummary(object):
    """
    Provides a summary of a test generation trial.
    """
    @staticmethod
    def from_json(jsn):
        """
        Constructs a summary of a past test generation trial from its
        JSON-based description.
        """
        jsn = jsn['summary']
        systm = System.from_json(jsn['settings']['system'])
        image = jsn['settings']['image']

        resource_usage = ResourceUsage.from_json(jsn['resources']['used'])
        resource_limits = ResourceLimits.from_json(jsn['resources']['limits'])

        history = \
            [Mission.from_json(m['mission']) for m in jsn['history']]
        failures = \
            set(Mission.from_json(m['mission']) for m in jsn['failures'])

        outcomes = \
            [(h['mission'], h['outcome']) for h in jsn['history']]
        outcomes = \
            [(Mission.from_json(m), MissionOutcome.from_json(o)) for (m, o) in outcomes]
        outcomes = {m: o for (m, o) in outcomes}

        return BugDetectorSummary(systm, image, history, outcomes, failures, resource_usage, resource_limits)


    def __init__(self, systm, image, history, outcomes, failures, resource_usage, resource_limits):
        """
        Constructs a summary of a bug detection process.

        :params resourceUsage:  a description of the resources consumed during \
                    the bug detection process.
        :params resourceLimits: a description of the resources limits that \
                    were imposed during the bug detection process.
        """
        assert (isinstance(systm, System))
        assert (isinstance(image, str) or isinstance(image, unicode))
        assert (isinstance(resourceUsage, ResourceUsage))
        assert (isinstance(resourceLimits, ResourceLimits))
        assert (isinstance(history, list))
        assert (isinstance(outcomes, dict))
        assert (isinstance(failures, set))
        assert (all(isinstance(m, Mission) for m in failures))

        self.__systm = systm
        self.__image = image
        self.__history = history
        self.__outcomes = outcomes
        self.__failures = failures
        self.__resource_usage = copy.copy(resource_usage)
        self.__resource_limits = resource_limits


    def to_json(self):
        """
        Serialises this summary into a JSON format.
        """
        resources = {
            'used': self.__resourceUsage.to_json(),
            'limits': self.__resourceLimits.to_json()
        }

        history = [(m, self.__outcomes[m]) for m in self.__history]
        history = [{'mission': m.to_json(), 'outcome': o.to_json()} for (m, o) in history]


        failures = [(m, self.__outcomes[m]) for m in self.__failures]
        failures = [{'mission': m.to_json(), 'outcome': o.to_json()} for (m, o) in failures]


        summary = {
            'settings': {
                'system': self.__systm.to_json(),
                'image': self.__image
            },
            'resources': resources,
            'history': history,
            'failures': failures
        }

        return {'summary': summary}

 
    @property
    def num_missions(self):
        return len(self.__history)

    
    @property
    def num_failures(self):
        return len(self.__failures)

    
    @property
    def image(self):
        return self.__image


    @property
    def system(self):
        return self.__systm

    
    @property
    def history(self):
        return self.__history[:]


    def outcome(self, m):
        return self.__outcomes[m]

    
    @property
    def outcomes(self):
        return self.__outcomes.copy()

    
    @property
    def failures(self):
        return self.__failures.copy()


    @property
    def resource_usage(self):
        return copy.copy(self.__resource_usage)


    @property
    def resource_limits(self):
        return self.__resource_limits


class MissionPoolWorker(threading.Thread):
    def __init__(self, detector):
        super(MissionPoolWorker, self).__init__()
        print("creating worker...")
        self.daemon = True # mark as a daemon thread
        self.__detector = detector
        self.__container = mgr.createContainer(self.__detector.system,
                                               self.__detector.image)
        self.__reset_counter()
        

    def __reset_counter(self):
        self.__counter = 0
        self.__reset = random.randint(3, 5) # TODO: use RNG


    def __prepare_container(self):
        if self.__counter == self.__reset:
            self.__reset_counter()
            self.__container.reset()
        self.__counter += 1


    def run(self):
        print("running worker: {}".format(self))
        #try:
        while True:
            m = self.__detector.get_next_mission()
            if m is None:
                return
            self.__prepare_container()
            self.__detector.execute_mission(m, self.__container)
        #finally:
        #    self.shutdown()


    def shutdown(self):
        print("shutting down worker: {}".format(self))
        if self.__container is not None:
            mgr.destroy_container(self.__container)
            self.__container = None


class BugDetector(object):
    """
    Bug detectors are responsible for finding bugs in a given system under test.
    """
    def __init__(self, threads = 1, action_generators = [], max_num_actions = 10):
        assert isinstance(max_num_actions, int)
        assert (max_num_actions >= 1)
        assert isinstance(threads, int)
        assert (threads >= 1)
        assert isinstance(action_generators, list)
        assert all(isinstance(g, ActionGenerator) for g in action_generators)

        self._rng = None
        self.__max_num_actions = max_num_actions
        self._fetch_lock = threading.Lock()
        self._contents_lock = threading.Lock()

        # transform the list of generators into a dictionary, indexed by the
        # name of the associated action schema
        self.__threads = threads
        self.__action_generators = {}
        for g in action_generators:
            name = g.schema_name
            assert not (name in self.__action_generators)
            self.__action_generators[name] = g


    def get_next_mission(self):
        self._fetch_lock.acquire()
        try:
            self.tick()

            # check if there are no jobs left
            if self.exhausted():
                return None

            # RANDOM:
            self.__resource_usage.num_missions += 1
            return self.generate_mission()

        finally:
            self._fetch_lock.release()


    def prepare(self, systm, image, seed, resource_limits):
        """
        Prepares the state of the bug detector immediately before beginning a
        bug detection trial.
        """
        self.__systm = systm
        self.__image = image
        self.__resource_limits = resource_limits
        self.__history = []
        self.__outcomes = {}
        self.__failures = set()
        self._rng = random.Random(seed)
            

    def exhausted(self):
        """
        Used to determine whether the resource limit for the current bug
        detection session has been hit.
        """
        return self.__resource_limits.reached(self.__resource_usage)


    def detect(self, systm, image, seed, resource_limits):
        """

        :param      systm: the system under test
        :param      image: the name of the Dockerfile that should be used to \
                        containerise the system under test
        :param      seed:   seed for the RNG
        :param      resource_limits: a description of the resources available \
                        to the detection process, given as a ResourceLimits \
                        object

        :returns    a summary of the detection process in the form of a \
                    BugDetectionSummary object
        """
        try:
            print("Preparing...")
            self.prepare(systm, image, seed, resource_limits)
            print("Prepared")

            # initialise worker threads
            self.__workers = []
            print("constructing workers...")
            for _ in range(self.__threads):
                self.__workers.append(MissionPoolWorker(self))
            print("constructed workers")
            
            # begin tracking resource usage
            self.__resource_usage = ResourceUsage()
            self.__start_time = timeit.default_timer()

            print("starting workers...")
            for w in self.__workers:
                w.start()
            print("started all workers")
            while True:
                if not any(w.is_alive() for w in self.__workers):
                    break
                time.sleep(0.2)

            self.tick()
            return self.summarise()
        finally:
            print("shutting down...")
            for worker in self.__workers:
                print("killing worker: {}".format(worker))
                worker.shutdown()
            self.__workers = []


    def tick(self):
        self.__resourceUsage.running_time = \
            timeit.default_timer() - self.__start_time


    def summarise(self):
        """
        Returns a summary of the last bug detection trial.
        """
        return BugDetectorSummary(self.__systm,
                                  self.__image,
                                  self.__history,
                                  self.__outcomes,
                                  self.__failures,
                                  self.__resource_usage,
                                  self.__resource_limits)

    def get_next_mission(self):
        self._fetch_lock.acquire()
        try:
            while True:
                self.tick()

                # check if there are no jobs left
                if self.exhausted():
                    return None

                # RANDOM:
                self.__resource_usage.num_missions += 1
                return self.generate_mission()

        finally:
            self._fetch_lock.release()


    @property
    def max_num_actions(self):
        return self.__max_num_actions


    @property
    def system(self):
        return self.__systm


    @property
    def image(self):
        return self.__image

    
    @property
    def resource_usage(self):
        return self.__resource_usage


    @property
    def num_threads(self):
        """
        The number of threads allocated to this test generator.
        """
        return self.__threads

    
    def executed_path(self, m):
        """
        Returns the path that was taken when a given mission was executed.
        """
        if m.is_empty():
            return BranchPath([])
        outcome = self.__outcomes[m]
        return outcome.executed_path()


    @property
    def end_state(self, m):
        """
        Returns the end state after executing a given mission.
        """
        assert isinstance(m, Mission)
        if m.is_empty():
            return m.initial_state
        outcome = self.__outcomes[m]
        return outcome.end_state


    def get_generator(self, schema):
        """
        Returns an available generator for a given action schema if there are
        non then it returns None.
        """
        name = schema.name
        if name in self.__action_generators:
            return self.__action_generators[name]
        return None


    def generate_mission(self, rng):
        raise NotImplementedError


    def execute_mission(self, mission, container):
        print("executing mission...")
        outcome = container.execute(mission)
        self.record_outcome(mission, outcome)
        print("finished mission!")
        return outcome


    def record_outcome(self, mission, outcome):
        """
        Records the outcome of a given mission. The mission is logged to the
        history, and its outcome is stored in the outcome dictionary. If the
        mission failed, the mission is also added to the set of failed
        missions.
        """
        self.__history.append(mission)
        self.__outcomes[mission] = outcome

        if outcome.failed():
            self.__failures.add(mission)
