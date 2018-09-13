__all__ = ['ParachuteSchema', 'ParachuteNormally']

import time
import math

from pymavlink import mavutil

from ...state import State
from ...specification import Specification
from ...environment import Environment
from ...action import ActionSchema, Parameter, Action
from ...branch import Branch, IdleBranch
from ...valueRange import DiscreteValueRange


class ParachuteSchema(ActionSchema):
    def __init__(self):
        parameters = [
            # 0=disable, 1=enable, 2=release
            Parameter('parachute_action', DiscreteValueRange([0, 1, 2]))
        ]
        branches = [
            ParachuteNormally(self, parameters),
            IdleBranch(self, parameters)
        ]
        super(ParachuteSchema, self).__init__('parachute',
                                              parameters,
                                              branches)

    def dispatch(self,
                 sandbox: 'Sandbox',
                 action: Action,
                 state: State,
                 environment: Environment
                 ) -> None:
        vehicle = sandbox.connection
        msg = vehicle.message_factory.command_long_encode(
            0, 0,
            mavutil.mavlink.MAV_CMD_DO_PARACHUTE,
            0, action['parachute_action'], 0, 0, 0, 0, 0, 0)
        vehicle.send_mavlink(msg)


class ParachuteNormally(Branch):
    def __init__(self, schema, parameters):
        specification = Specification(parameters,
            """
            (and (= $parachute_action 2)
                (= _armed true)
                (= _mode "GUIDED")
                (> _altitude 10.0)) 
            """,
            """
            (and (= __armed false)
                (< __altitude 0.3)
                (= __vz 0.0))
            """,
            None) # TODO: the minimum altitude is specified in system. We need a way to use it.
        super(ParachuteNormally, self).__init__("normal", schema, specification)

    def timeout(self, system, action, state, environment):
        timeout = state['altitude'] * system.time_per_metre_travelled
        timeout += system.constant_timeout_offset
        return timeout

#    def postcondition(self,
#                      system,
#                      action,
#                      state_before,
#                      state_after,
#                      environment):
#        v = system.variable
#        return not state_after['armed'] and \
#            v('altitude').lt(state_after['altitude'], 0.3) and \
#            v('vz').eq(state_after['vz'], 0.0)
#
#    def precondition(self, system, action, state, environment):
#        return action['parachute_action'] == 2 and \
#            self.is_satisfiable(system, state, environment)
#
#    def is_satisfiable(self, system, state, environment):
#        v = system.variable
#        return state['armed'] and \
#            state['mode'] == 'GUIDED' and \
#            v('altitude').gt(state['altitude'], system.min_parachute_alt)

    def generate(self, system, state, env, rng):
        return self.schema.generate(rng)
