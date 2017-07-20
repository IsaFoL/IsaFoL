#!/bin/bash

# test -n "$FIELDS" || FIELDS="drat gratgen-j1 gratchk-j1 gratgen-j4 gratchk-j4 gratgen-j8 gratchk-j8 gratgen-j12 gratchk-j12 gratgen-j16 gratchk-j16"
test -n "$FIELDS" || FIELDS="drat lrat gratgen-j1 gratchk-j1 gratgen-j8 gratchk-j8"

test -n "$PROBLEMS" || PROBLEMS=`cat sc2016_riss6_unsat.list`

test -n "$LOGDIR" || LOGDIR="logs/2017-06-combined/riss6"

OLDDIR="$PWD"


cd $LOGDIR
. $OLDDIR/timelog.inc.sh
cd $OLDDIR

