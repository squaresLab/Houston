all: build

build: 
	docker build -t robotest .

.PHONY: build
