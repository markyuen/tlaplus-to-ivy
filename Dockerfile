FROM python:2.7.18-slim-buster

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    cmake \
    g++ \
    git \
    libreadline-dev \
    libssl-dev \
    pkg-config \
    python-ply \
    python-pygraphviz \
    python-tk \
    tix \
    && rm -rf /var/cache/apt/lists

RUN pip install pyparsing==2.1.4 pexpect \
    && git clone --recurse-submodules https://github.com/kenmcmil/ivy.git \
    && cd ivy \
    && git checkout cea153424ba6ad6957036d98bc88f63f21df4173 \
    && python build_submodules.py \
    && python setup.py install

RUN apt-get remove -y \
    g++ \
    git \
    libreadline-dev \
    libssl-dev \
    pkg-config \
    && apt-get autoremove -y \
    && apt-get remove -y cmake

CMD ["sleep", "infinity"]
