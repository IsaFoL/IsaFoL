#!/bin/bash

USE_COLORS=true

function prstat {
  if test -f $1; then
    gawk '
      function n5(t) {
      
      }
    
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
        ok=0
      }
    
      /^s VERIFIED( UNSAT)?$/ {ok=1}
      /^\tElapsed \(wall clock\) time/ {
        t=time2s($8)
        printf "%10.2f" , t
      }  
      END {
        if (ok != 1) printf "ERR"
      }
    ' $1
  fi
}

function pr_fst_col {
  if $USE_COLORS; then tput sc; fi
  echo -n "$1"
  if $USE_COLORS; then tput rc; tput cuf 49; echo -n " "; fi
}

function prheader {
  pr_fst_col "Name"
  echo -e ",       drat,      gg-j1,      gc-j1,         gg,         gc,   drat/gc"
}


function pr_line {
  NAME=$1
  BASENAME=`basename $NAME`


  if $USE_COLORS; then 
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    NC='\033[0m' # No Color
  else
    RED=""
    GREEN=""
    NC=""
  fi
  
  
  drat=`prstat "$NAME.drat.log"`
  gg1=`prstat "$NAME.gratgen-j1.log"`
  gc1=`prstat "$NAME.gratchk-j1.log"`
  gg=`prstat "$NAME.gratgen.log"`
  gc=`prstat "$NAME.gratchk.log"`

  prep_str=""
  app_str=""
  dr_ratio=""
  
  if [[ "$drat" ]] && [[ "$gg1" ]] && [[ "$gg1" != "ERR" ]]; then
    dr_ratio=`echo "$drat * 100 / $gg1" | bc`
    dr_bad=`echo "$dr_ratio < 80" | bc`
    dr_good=`echo "$dr_ratio > 120" | bc`
    
    SUM_DRAT=`echo "$SUM_DRAT + $drat" | bc`
    SUM_GG1=`echo "$SUM_GG1 + $gg1" | bc`

    SUM_GGC1=`echo "$SUM_GGC1 + $gg1 + $gc1" | bc`
    SUM_GGC=`echo "$SUM_GGC + $gg + $gc" | bc`

    SUM_GC1=`echo "$SUM_GC1 + $gc1" | bc`
    SUM_GC=`echo "$SUM_GC + $gc" | bc`
    
    if [[ "$gg" != "ERR" ]]; then
      SUM_GG=`echo "$SUM_GG + $gg" | bc`
    fi
    
    if [[ $dr_bad == 1 ]]; then prep_str="$RED"; app_str="$NC"; fi
    if [[ $dr_good == 1 ]]; then prep_str="$GREEN"; app_str="$NC"; fi
    
    echo -ne "$prep_str"
    pr_fst_col "$BASENAME"
    echo -e "  $drat, $gg1, $gc1, $gg, $gc,  $dr_ratio$app_str"
  fi
  
}

prheader "$BASENAME"

if [ $# -eq 0 ]; then
  NAMES=`cat sc2016_cmsat5_unsat.list`
  DIR="out/cmsat5_main2/default/"
else
  NAMES=$@
  DIR=""
fi


SUM_DRAT=0
SUM_GG1=0
SUM_GG=0
SUM_GGC1=0
SUM_GGC=0
SUM_GC1=0
SUM_GC=0

for NAME in $NAMES; do
  NAME=${NAME%.cnf}

  if [[ "$NAME" == "" ]]; then 
    echo "Empty name?"
    exit 1
  fi

  pr_line "$DIR$NAME"

#   if test -t 1; then tput sc; fi
#   echo -n "$BASENAME "
#   if test -t 1; then tput rc; tput cuf 49; echo -n " "; fi
#   prstat "$NAME.drat.log"
#   prstat "$NAME.gratgen-j1.log"
#   prstat "$NAME.gratchk-j1.log"
#   prstat "$NAME.gratgen.log"
#   prstat "$NAME.gratchk.log"
#   echo
done

echo "$SUM_DRAT   $SUM_GG1   $SUM_GG    $SUM_GGC1    $SUM_GGC   $SUM_GC1     $SUM_GC"
