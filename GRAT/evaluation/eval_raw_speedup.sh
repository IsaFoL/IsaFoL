#!/bin/bash


function wct() {
  gawk '
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
    
    /^\tElapsed \(wall clock\) time/ {
      t=time2s($8)
      printf "%10.0f" , t
    }  
  ' $1
}

function bwd() {
  gawk '$3=="bwd:" {printf "%10.0f", $4/1000}' $1
}


for d in $@; do ls -1 $d/*.gratgen-j1.log; done |\
while read f; do 
  f=${f%.gratgen-j1.log};
  
  g1=$f.gratgen-j1.log
  g8=$f.gratgen-j8.log
  c1=$f.gratchk-j1.log
  c8=$f.gratchk-j8.log

  #       1          2         3         4         5         6
  echo `wct $g1` `wct $g8` `wct $c1` `wct $c8` `bwd $g1` `bwd $g8`
done |\
gawk '
  $1 {
    g1=$1
    g8=$2
    c1=$3
    c8=$4
    bg1=$5
    bg8=$6
  
    tot1=g1+c1
    tot8=g8+c8

    gtot1=gtot1+tot1
    gtot8=gtot8+tot8
    
    if (bg8>0 && tot8>0 && g1>100) {
      q=tot1/tot8
      bq=bg1/bg8
      num++; 
      val = val + q; 
      bval = bval + bq; 
    }
  }   
  END { 
    if (num>0) {
      print "Totals:   " val " / " num " = " val/num; 
      print "Only Bwd: " bval " / " num " = " bval/num; 
      print "Sum-Totals: " gtot1 " / " gtot8 " = " gtot1/gtot8
    }
  }'
