#!/bin/bash

# Build release tgz package for gratgen

FILES="CMakeLists.txt Doxyfile gratgen.cpp README.md doc"

tar -czf gratgen.tgz --transform='s|^|gratgen/|' $FILES
