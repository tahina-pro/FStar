#!/usr/bin/env bash

set -x

set -e # abort on errors

target=$1
threads=$2
branchname=$3

build_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$build_home"/build_funs.sh

rootPath=$(pwd)
result_file="result.txt"
status_file="status.txt"
ORANGE_FILE="orange_file.txt"
out_file="log.txt"
{ { { { { { build_fstar $target ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDERR]!' ; } 3>&1 1>&2 2>&3 ; } | sed -u 's!^![STDOUT]!' ; } 2>&1 ; } | awk '{ print strftime("[%Y-%m-%d %H:%M:%S]"), $0 }' | tee $out_file
