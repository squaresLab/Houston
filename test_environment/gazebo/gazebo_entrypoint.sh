#!/bin/bash
# setup gazebo environment
export "INSTALL_SPACE=/opt/sasc"
source "${INSTALL_SPACE}/setup.bash"
source "${INSTALL_SPACE}/share/gazebo-8/setup.sh"
source "${INSTALL_SPACE}/share/uctf/setup.sh"
export "GAZEBO_MODEL_PATH=/opt/sasc/share/gazebo_models"
exec "$@"
