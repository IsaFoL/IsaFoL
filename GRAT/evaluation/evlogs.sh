#!/bin/bash

ORIG_DIR=$PWD
DIR="$HOME/sat_solving"
ODIR="$DIR/out/Riss6/noPP_DRAT"

cd "$DIR"
NUM=`cat sc2016_riss6_unsat.list | wc -l`
cd $ODIR
DONE=`grep -l "^s VERIFIED" *.gratchk-j8.log | wc -l`

echo Successfully processed $DONE of $NUM problems

echo PENDING/ERROR
egrep -L "^s VERIFIED" *lrat.log
egrep -L "^.?s VERIFIED" *drat.log *gratgen-j*.log *gratchk-j*.log

echo "======================"

echo -n "LRAT time:    "; cat *lrat.log | $ORIG_DIR/wc_summary.gawk
echo -n "DRAT time:    "; cat *drat.log | $ORIG_DIR/wc_summary.gawk
echo -n "GRAT-j1 time: "; cat *gratgen-j1.log *gratchk-j1.log | $ORIG_DIR/wc_summary.gawk
echo -n "  gen:        "; cat *gratgen-j1.log | $ORIG_DIR/wc_summary.gawk
echo -n "  chk:        "; cat *gratchk-j1.log | $ORIG_DIR/wc_summary.gawk
echo -n "GRAT-j8 time: "; cat *gratgen-j8.log *gratchk-j8.log | $ORIG_DIR/wc_summary.gawk
echo -n "  gen:        "; cat *gratgen-j8.log | $ORIG_DIR/wc_summary.gawk
echo -n "  chk:        "; cat *gratchk-j8.log | $ORIG_DIR/wc_summary.gawk

echo "======================"

cd $ORIG_DIR
