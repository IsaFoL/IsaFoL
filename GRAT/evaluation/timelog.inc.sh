SUBFIELDS="user-time/s sys-time(s) wall-time/s mem/KiB"

function pr_log_info {
  if test -f $1; then
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
    
      BEGIN {
        user_time="--"
        sys_time="--"
        wall_time="--"
        used_mem="--"
      }

      /^\tUser time \(seconds\)/ {
        user_time=sprintf("%5.1f", $4)
      }  
      
      /^\tSystem time \(seconds\)/ {
        sys_time=sprintf("%5.1f", $4)
      }  
      
      /^\tElapsed \(wall clock\) time/ {
        wall_time=sprintf("%5.1f", time2s($8))
      }  
      
      /^\tMaximum resident set size \(kbytes\):/ {
        used_mem=sprintf("%9.1f",$6)
      }
      
      END {
        printf "%s, %s, %s, %s, ", user_time, sys_time, wall_time, used_mem
      }
    ' $1
  else
    echo -n "--    , --    , --    , --    , "
  fi
}

if test ! -n "$NOHEADER"; then
  echo -n "problem, " $EXTRAFIELDS
  for i in $FIELDS; do
    for j in $SUBFIELDS; do
      echo -n "$i-$j, "
    done
  done
  echo
fi

for i in $PROBLEMS; do
  BASENAME=${i%.cnf}
  echo -n "$BASENAME, " $EXTRAFIELDSV
  for j in $FIELDS; do
    LOGFILE="$BASENAME.$j.log"
    pr_log_info $LOGFILE
  done
  echo
done
