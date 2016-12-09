#!/usr/bin/env bash

# script for Lazy Small Check
# use: `lsc.sh file.smt2 timeout`

TIP_FILE=$1
TIMEOUT=$2

BASENAME=`basename $1 .smt2`
ROOT=/tmp/lsc/`dirname $1`/
mkdir -p $ROOT
HS_FILE=$ROOT/$BASENAME.hs
BINARY=$ROOT/$BASENAME

tip --haskell-lazysc $TIP_FILE > $HS_FILE
ghc --make $HS_FILE -o $BINARY
ulimit -t $2 ; exec $BINARY



