#!/usr/bin/gawk -f

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
  wall_time=0
}

/^\tElapsed \(wall clock\) time/ {
  wall_time=wall_time + time2s($8)
}  

END {
  printf("%5.0f\n",wall_time)
}
