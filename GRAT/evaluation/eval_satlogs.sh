#!/bin/bash

test -n "$FIELDS" || FIELDS="sat"
test -n "$PROBLEMS" || PROBLEMS=`cat sc2016_cmsat5_sat.list`


cd logs
. ../timelog.inc.sh
cd ..
