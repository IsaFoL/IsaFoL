#!/usr/bin/gawk -f


BEGIN {
  peek_user="lammich"
  current_pu = 0
  current_ou = 0
  
  intf_start = ""
  intf_cycles = 0
}

function log_cycle() {
  if (current_pu != 0 && current_ou != 0) {
    if (intf_cycles == 0) intf_start = current
    intf_cycles++
  } else if (intf_cycles>0) {
    if (intf_cycles >= 10) {
      print intf_start " -- " current " (" intf_cycles ")"
      for (i in times) print i " " times[i] " " (times[i] / intf_cycles)
    }
    
    intf_cycles = 0
    delete times
    
  }
}


$1~/[A-Za-z]+/ && $2~/[0-9]+/ {
  if ($2!=0) {
    times[$1] += $2
    
    if ($1 == peek_user) 
      current_pu = 1
    else 
      current_ou = 1
  }
}

$1~/[0-9]+-[0-9]+-[0-9]+T*/ { 
  log_cycle();
  current=$1;
  current_pu = 0;
  current_ou = 0;
}


END {
  current_pu = 0
  current_ou = 0
  log_cycle()
}
