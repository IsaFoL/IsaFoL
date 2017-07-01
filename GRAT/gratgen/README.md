# GRATgen
Check DRAT certificate and emit GRAT certificate.

## Build
Run 

    cmake .
    make
    make install

this should generate a build system, build the executable gratgen, and install it in $HOME/bin by default.

If you do not like heavy make scripts, just run:

    g++ -O3 -DNDEBUG -std=c++11 -pthread -o gratgen gratgen.cpp

and make sure you have the [Boost](http://www.boost.org/) libraries on your include path.
    

## Usage
  For short:

    gratgen formula.cnf formula.drat [-o formula.gratp] [-l formula.gratl] [-j num_threads]

  run gratgen without arguments to get a list of all available options.

## Documentation
Can be found in the [doc/](doc/html/index.html) folder.
