#!/bin/bash

# test -n "$FIELDS" || FIELDS="drat gratgen-j1 gratchk-j1 gratgen-j4 gratchk-j4 gratgen-j8 gratchk-j8 gratgen-j12 gratchk-j12 gratgen-j16 gratchk-j16"
test -n "$FIELDS" || FIELDS="drat lrat gratgen-j1 gratchk-j1 gratgen-j8 gratchk-j8"

test -n "$PROBLEMS" || PROBLEMS=`cat sc2017_maple_unsat.list`

test -n "$LOGDIR" || LOGDIR="logs/2018-01-maple"

OLDDIR="$PWD"


cd $LOGDIR
. $OLDDIR/timelog.inc.sh
cd $OLDDIR

