# Setting up and running the project with Docker

In case you have a lot of trouble installing polyml and HOL, you can use Docker to run the project.

1. Install Docker Desktop for your platform from [here](https://docs.docker.com/desktop/).

1. Create a `Dockerfile` in the root of the project with the following content:

  ```Dockerfile
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
```

1. Run this command to build the docker image:

```sh
docker build . -t hol  # -t <name of docker image, can be anything you like>
```
This should take 10-20 minutes.

1. Run Holmake, pointing the cwd of the docker image (`-w`) to the directory that you want to run Holmake in. For example, this runs `Holmake` in the `spec/` directory:
```sh
docker run -v $PWD:/app -w /app/spec hol Holmake
```
