#!/bin/bash

echo "problem,  drat-size/B,  grat-size-j1/B,   grat-size/B,  #drat-lemmas,  #grat-lemmas-j1, #grat-lemmas"

for i in $@; do
  NAME=${i%.cnf}
  echo -n "$NAME"
  stat --printf=", %s" $NAME.drat
  stat --printf=", %s" $NAME.grat-j1
  stat --printf=", %s" $NAME.grat
  wc -l $NAME.drat | awk '{printf ", " $1}'
  wc -l $NAME.grat-j1 | awk '{printf ", " $1}'
  wc -l $NAME.grat | awk '{printf ", " $1}'
  echo
done
