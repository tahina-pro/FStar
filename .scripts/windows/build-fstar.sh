#!/usr/bin/env bash
# This script builds and tests the F* binary package, assuming that
# all build dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/.scripts/windows$' > /dev/null
cd ../..
.scripts/test-package.sh
