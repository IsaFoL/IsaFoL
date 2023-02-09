#!/bin/bash

# Build release tgz package for gratgen

FILES="code/*.sml code/*.mlb code/README.md code/Makefile    *.thy ROOT document/root.tex README.md output/*.pdf"

tar -czf gratchk.tgz --transform='s|^|gratchk/|' $FILES
