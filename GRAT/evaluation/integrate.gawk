#!/usr/bin/gawk -f

BEGIN {
  count=0
  last=0
}

{
  this=$1
  
  if (this>last && last!=0) {
    print count "\t " last 
  }

  last=this
  count++
}

END {
  print count "\t " last 
}
