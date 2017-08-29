FROM alpine:latest

RUN apk add --no-cache \
        python \
        python-dev \
        py-pip \
        py-setuptools
RUN pip install requests pexpect

RUN mkdir -p /tmp/houston
WORKDIR /tmp/houston
ADD setup.py setup.py
ADD houston houston
ADD test test

RUN ./setup.py install && \
    rm -rf /tmp/houston

VOLUME /usr/lib/python2.7/dist-packages/requests
VOLUME /usr/lib/python2.7/dist-packages/pexpect
VOLUME /usr/local/bin/houstonserver
VOLUME /usr/local/lib/python2.7/dist-packages/houston-0.0.1-py2.7.egg
