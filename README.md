# tlaplus-to-ivy

This repository contains TLA+ and Ivy specifications for the Suzuki-Kasami distributed mutual exclusion algorithm [[1985]](https://doi.org/10.1145/6110.214406) and the Network-Ordered Paxos (NOPaxos) distributed consensus protocol [[2016]](https://dl.acm.org/doi/10.5555/3026877.3026914). It is a bit troublesome to set up an environment to verify Ivy specifications (primarily because it requires Python 2.7), so a Dockerfile is provided to build a basic container that can run the Ivy tool. This work is completed in part for the Yale-NUS undergraduate thesis Capstone project.

### Model Checking with TLA+

- Install the TLA+ extension in VSCode to model-check a TLA+ specification with its configuration file
- The original `NOPaxos.tla` specification is sourced from the authors of the NOPaxos paper [[source]](https://github.com/UWSysLab/NOPaxosTLA)
    + We provide a configuration file for ease of use
    + Any additions to the specification file are noted in our version

### Running Ivy with Docker

- Install Docker Desktop
- Run `docker-compose up -d` in this directory to build the image and start the container
    + **A note of caution:** the `ivy` image is about 1.91GB in size and will likely take 15+ minutes to build
    + Run `docker-compose stop` to pause the container
    + Run `docker-compose start` to restart a paused container
    + Run `docker-compose down` to remove the container
- Run `docker-compose exec ivy bash` to enter a shell on the container
    + The local `ivy/` folder is mounted in the container at `/src/`
    + Verify an Ivy file with `ivy_check [filename.ivy]`
