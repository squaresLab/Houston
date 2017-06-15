all: build

build:
	docker build -t art:roscore   roscore_docker/
	docker build -t art:mavros    mavros_docker/
	docker build -t art:ardupilot ardupilot_docker/

.PHONY: build
