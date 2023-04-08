#!/usr/bin/env bash

# Install Z3 and the opam package dependencies
# We use the Everest script; this will automatically install OCaml.
# We assume an everest checkout in the same directory as this script.
# The GitHub Actions workflow should take care of cloning everest.
cwd=$(cd $(dirname $0); pwd -P)
cd $cwd/everest
./everest --yes z3 opam
