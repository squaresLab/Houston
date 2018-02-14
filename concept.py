import docker
import dronekit

# connect to the Docker daemon
client = docker.client.from_env()
print("AAA")

# provision a container from an ArduPilot image
image_name = "squareslab/ardubugs:base"
container = client.containers.create(image_name, "/bin/bash", stdin_open=True, detach=True, working_dir="/experiment/source")
container.start()
print(container.status)
print("BBB")

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
print("CCC")

# connect to the SITL from the host via dronekit
#port = 14550
#url = "{}:{}".format(container.ip_address, port)
#dronekit.connect(url, wait_ready=True)
