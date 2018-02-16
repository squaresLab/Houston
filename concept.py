from time import sleep
import threading
import sys
import docker
import dronekit


def launch_sitl(container):
    model = "rover"
    speedup = "1.0"
    home = "-35.362938,149.165085,584,270"
    cmd = 'build/sitl/bin/ardurover --model "{}" --speedup "{}" --home "{}"'.format(model, speedup, home)
    print("Executing: {}".format(cmd))
    (_, output_stream) = container.exec_run(cmd, stream=True)
    for line in output_stream:
        line = line.decode(sys.stdout.encoding).rstrip('\n')
        print(line, flush=True)


# connect to the Docker daemon
client = docker.client.from_env()
api_client = docker.APIClient(base_url='unix://var/run/docker.sock')

# provision a container from an ArduPilot image
image_name = "squareslab/ardubugs:base"
container = client.containers.create(image_name, "/bin/bash", stdin_open=True, detach=True, working_dir="/experiment/source")
container.start()
print("Container status: {}".format(container.status))

# build SITL
print("Configuring...")
cmd = "./waf configure"
container.exec_run(cmd)

cmd = "./waf build -j8"
print("Building...")
container.exec_run(cmd)
print("Built")

# use a separate thread to launch the SITL
sitl_thread = threading.Thread(target=launch_sitl, args=(container,))
sitl_thread.start()

sleep(5)

# connect to the SITL from the host via dronekit
port = 5760
container_info = api_client.inspect_container(container.id)
ip_address = container_info['NetworkSettings']['IPAddress']
url = "tcp:{}:{}".format(ip_address, port)
print("Attempting to connect to: {}".format(url))

try:
    vehicle = dronekit.connect(url, wait_ready=True)
except dronekit.APIException as e:
    print("FAILED {}".format(str(e)))
    raise e

print("Armed:{}, Mode:{}".format(vehicle.armed, vehicle.mode.name))
vehicle.mode = dronekit.VehicleMode('GUIDED')
vehicle.armed = True
print("Armed:{}, Mode:{}".format(vehicle.armed, vehicle.mode.name))
loc = dronekit.LocationGlobalRelative(10, 10, 0)
vehicle.simple_goto(loc)

container.stop()
