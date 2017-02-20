#!/bin/bash

test -n "$FIELDS" || FIELDS="drat gratgen-j1 gratchk-j1 gratgen-j4 gratchk-j4 gratgen-j8 gratchk-j8 gratgen-j12 gratchk-j12 gratgen-j16 gratchk-j16"

test -n "$PROBLEMS" || PROBLEMS=`cat sc2016_cmsat5_unsat.list`

cd logs
. ../timelog.inc.sh
cd ..

