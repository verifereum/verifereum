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

1. Create a `docker-compose.yml` file in the root of the project:

```yaml
services:
  verifereum:
    image: verifereum
    build:
      context: .
      dockerfile: Dockerfile
      tags:
        - verifereum
    volumes:
      - .:/src
    working_dir: /src
```

1. Run this command to initialize the environment and enter the shell. On its first run it'll build the image which could take a while:

```sh
docker compose run verifereum
```

1. Within the shell, run this to build the project and run the tests:

```sh
Holmake
```
