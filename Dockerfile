# Keep in sync with https://github.com/CakeML/pure/blob/master/.github/Dockerfile
# we copied it over because there's certain deps we don't need
FROM ubuntu:20.04

WORKDIR /home

# Install pre-requisites
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive \
    apt-get install -y git build-essential gcc-10

# build poly
RUN git clone https://github.com/polyml/polyml && \
    cd polyml && \
    ./configure --prefix=/usr && \
    make && make compiler && make install

## build HOL
RUN git clone https://github.com/HOL-Theorem-Prover/HOL && \
    cd HOL && \
    poly --script tools/smart-configure.sml && \
    bin/build

# set environment variable
ENV HOLDIR=/home/HOL
# update path
ENV PATH=$HOLDIR/bin:$PATH

