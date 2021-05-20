FROM ubuntu:20.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install --yes --no-install-recommends sudo curl git
RUN curl -fsSL https://deb.nodesource.com/setup_14.x | sudo -E bash -
RUN apt-get install --yes --no-install-recommends npm

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME /home/test
WORKDIR $HOME

SHELL ["/bin/bash", "--login", "-c"]

RUN npm install esy
RUN echo export PATH=$HOME/node_modules/.bin:\$PATH >> $HOME/.bash_profile
RUN sudo apt-get install --yes --no-install-recommends xz-utils binutils gcc
RUN sudo apt-get update
RUN sudo apt-get install --yes --no-install-recommends libc6-dev
RUN sudo apt-get install --yes --no-install-recommends build-essential
RUN sudo apt-get install --yes --no-install-recommends m4

COPY --chown=test . fstar
WORKDIR $HOME/fstar
RUN esy install
RUN esy b dune build
