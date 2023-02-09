#!/bin/bash

# Build release tgz package for gratgen

FILES="*.sml *.mlb Makefile README.md"

tar -czf gratchk-sml.tgz --transform='s|^|gratchk-sml/|' $FILES
