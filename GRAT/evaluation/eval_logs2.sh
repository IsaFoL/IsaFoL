#!/bin/bash

# test -n "$FIELDS" || FIELDS="drat gratgen-j1 gratchk-j1 gratgen-j4 gratchk-j4 gratgen-j8 gratchk-j8 gratgen-j12 gratchk-j12 gratgen-j16 gratchk-j16"
test -n "$FIELDS" || FIELDS="drat gratgen-j1 gratchk-j1 gratgen-j8 gratchk-j8"

test -n "$PROBLEMS" || PROBLEMS=`cat sc2016_cmsat5_unsat.list sc2016_cmsat5_unsat_chkerr.list`

test -n "$LOGDIR" || LOGDIR="logs/2017-05-combined"

OLDDIR="$PWD"


cd $LOGDIR
. $OLDDIR/timelog.inc.sh
cd $OLDDIR

