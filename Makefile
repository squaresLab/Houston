all: build

build: 
	docker build -t houston .

.PHONY: build
