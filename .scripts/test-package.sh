#!/usr/bin/env bash

# Set the environment, where FSTAR_HOST_HOME is for building, and
# FSTAR_HOME is for testing.
unset FSTAR_HOME
FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)

# Build and test the package
. "$FSTAR_HOST_HOME/.scripts/test-package-aux.sh"
