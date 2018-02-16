from time import sleep
import docker
import dronekit

# connect to the Docker daemon
client = docker.client.from_env()

# provision a container from an ArduPilot image
image_name = "squareslab/ardubugs:base"
container = client.containers.create(image_name, "/bin/bash", stdin_open=True, detach=True, working_dir="/experiment/source")
container.start()
print("Container status: {}".format(container.status))

# build SITL
cmd = "./waf configure"
container.exec_run(cmd)

cmd = "./waf build -j8"
container.exec_run(cmd)


# start the SITL inside a container
model = "rover"
speedup = "1.0"
home = "-35.362938,149.165085,584,270"
cmd = 'build/sitl/bin/ardurover --model "{}" --speedup "{}" --home "{}"'.format(model, speedup, home)
container.exec_run(cmd, detach=True)

# connect to the SITL from the host via dronekit
port = 5760
container_info = docker.APIClient(base_url='unix://var/run/docker.sock').inspect_container(container.id)
ip_address = container_info['NetworkSettings']['IPAddress']
url = "tcp:{}:{}".format(ip_address, port)
print(url)
v = None
while not v:
    try:
        v = dronekit.connect(url, wait_ready=True) # it fails the first time!!
    except dronekit.APIException as e:
        sleep(10)
        print("FAILED {}".format(str(e)))

print("Armed:{}, Mode:{}".format(v.armed, v.mode.name))
v.mode = dronekit.VehicleMode('GUIDED')
v.armed = True
print("Armed:{}, Mode:{}".format(v.armed, v.mode.name))
#loc = dronekit.LocationGlobalRelative(10, 10, 0)
#v.simple_goto(loc)

container.stop()