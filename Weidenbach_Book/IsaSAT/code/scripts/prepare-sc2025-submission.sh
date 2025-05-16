#!/bin/bash

cp run.sh ../../../../
cp build.sh ../../../../

sed -i "s|../src|Weidenbach_Book/IsaSAT/code/src|g" ../../../../run.sh ../../../../build.sh