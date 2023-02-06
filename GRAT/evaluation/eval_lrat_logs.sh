#!/bin/bash


test -n "$PROBLEMS" || PROBLEMS=`cat sc2016_cmsat5_unsat.list sc2016_cmsat5_unsat_chkerr.list`

test -n "$LOGDIR" || LOGDIR="logs/2017-05-lrat-complete"

OLDDIR="$PWD"


function pr_log_info {
  if test -f $1.lrat.log; then
    cat $1.lrat.log $1.out | gawk '
      function time2s(t,       a,n) {
        n = split(t,a,":");
        if (n==2) {
          return a[1]*60 + a[2]
        } else if (n==3) {
          return a[1]*3600 + a[2]*60 + a[3]
        } else {
          return 0
        }
      }
    
      BEGIN {
        wall_time="--"
        drat_time="--"
        lrat_time="--"
      }

      /^\tElapsed \(wall clock\) time/ {
        wall_time=sprintf("%5.1f", time2s($8))
      }  
      
      /^; [0-9\.]+ seconds realtime/ {
        lrat_time=sprintf("%5.1f", $2)
      }
      
      /c verification time: / {
        drat_time=sprintf("%5.1f", $4)
      }
      
      
      END {
        printf "%s, %s, %s, ", wall_time, drat_time, lrat_time
      }
    '
  else
    echo -n "--    , --    , --   , "
  fi
}



echo "problem, overall-time, drat-time, lrat-time"

cd $LOGDIR

for i in $PROBLEMS; do
  BASENAME=${i%.cnf}
  echo -n "$BASENAME, "
  pr_log_info $BASENAME
  echo
done

cd $OLDDIR
