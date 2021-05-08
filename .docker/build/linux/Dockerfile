# syntax=docker/dockerfile:1.2

# Fstar build container

# Define on config.json what base container image build should use.
# By default it always look for the latest container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG DOCKERHUBPROJECT
ARG COMMITID
FROM ${DOCKERHUBPROJECT}everest-ci-linux:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG BUILDTARGET
ARG BRANCHNAME

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh

# Copy FSTAR source code.
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/

WORKDIR ${MYHOME}

# Remove extra files.
RUN rm ${MYHOME}/FStar/Dockerfile
RUN rm ${MYHOME}/FStar/build.sh
RUN rm ${MYHOME}/FStar/build_helper.sh
RUN rm ${MYHOME}/FStar/commitinfofilename.json

COPY --chown=everest build.sh ${MYHOME}/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/build_helper.sh
RUN chmod +x build_helper.sh

RUN --mount=type=ssh,id=everest_ssh ./build_helper.sh ${BUILDTARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} || true
