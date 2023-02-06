#!/bin/bash

FIELDS="sat"
EXTRAFIELDS="Solver, "


THIS_DIR="$PWD"


cd logs/2018-01-maple
EXTRAFIELDSV="Maple, "
PROBLEMS=`ls -1 *.sat.log | sed -re 's/\.sat\.log$//g'`
. ../../timelog.inc.sh
cd "$THIS_DIR"

cd logs/cmsat_satlogs
EXTRAFIELDSV="cmsat, "
PROBLEMS=`ls -1 *.sat.log | sed -re 's/\.sat\.log$//g'`
NOHEADER=true
. ../../timelog.inc.sh
cd "$THIS_DIR"

cd logs/riss6_satlogs
EXTRAFIELDSV="riss6, "
PROBLEMS=`ls -1 *.sat.log | sed -re 's/\.sat\.log$//g'`
NOHEADER=true
. ../../timelog.inc.sh
cd "$THIS_DIR"
