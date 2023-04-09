#!/usr/bin/env bash

set -e
set -x

# Add /usr/local/bin to the PATH (opam installs there)
echo "export PATH='/usr/local/bin:$PATH'" >> $HOME/.bash_profile
source $HOME/.bash_profile

# Install OCaml (inspired from the ./everest script)
wget 'https://github.com/fdopen/opam-repository-mingw/releases/download/0.0.0.2/opam64.tar.xz'
tar -xf 'opam64.tar.xz'
rm -f 'opam64.tar.xz'
bash opam64/install.sh
opam init default "https://github.com/fdopen/opam-repository-mingw.git#opam2" -c "ocaml-variants.4.12.0+mingw64c" --disable-sandboxing
echo '. "$HOME/.opam/opam-init/init.sh" > /dev/null 2>/dev/null' >> $HOME/.bash_profile
eval $(opam config env)

# Install Z3 (from the ./everest script)
# We use the Everest script to retrieve the list of opam packages.
# We assume an everest checkout in the same directory as this script.
# The GitHub Actions workflow should take care of cloning everest.
# We cannot use ./everest check because opam depext fails with:
# "The following packages are necessary: Bad file descriptor"
cwd=$(cd $(dirname $0); pwd -P)
cd $cwd/everest
./everest --yes z3

# Install the opam packages that F* depends on
# Skip z3, already installed via everest
grep -v z3 < $cwd/../fstar.opam > fstar-no-z3.opam
opam install --deps-only ./fstar-no-z3.opam
rm fstar-no-z3.opam
