# GRATgen
Check DRAT certificate and emit GRAT certificate.

## Build
Run 
    cmake .
    make

this should generate a build system and build the executable gratgen in the current folder.

If you do not like heavy make scripts, just run:
    g++ -O3 -DNDEBUG -std=c++11 -pthread -o gratgen gratgen.cpp


## Usage
  For short:
    gratgen formula.cnf formula.drat [-o formula.grat] [-j num_threads]

  run gratgen without arguments to get a list of all available options.

## Documentation
Can be found in the [doc/](doc/html/index.html) folder.
