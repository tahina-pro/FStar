#!/usr/bin/env bash

set -e
set -x

# Install Z3 and the opam package dependencies
# We use the Everest script; this will automatically install OCaml.
# We assume an everest checkout in the same directory as this script.
# The GitHub Actions workflow should take care of cloning everest.
cwd=$(cd $(dirname $0); pwd -P)
cd $cwd
echo "export PATH=/usr/local/bin:$PATH" >> $HOME/.bash_profile # opam installs there
source env.sh
cd $cwd/everest
./everest --yes check
