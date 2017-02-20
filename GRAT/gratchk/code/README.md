# GRATchk ML distribution

This folder contains the GRATchk Standard ML code. 

## Prerequisites
  * An [MLton](http://mlton.org/) compiler version >= 20100608 must be installed.
  * No Isabelle installation is required

## Building
  Just type 
     make
  to obtain a gratchk binary in the current folder. Or
      make install
  to install to <code>$HOME/bin</code>.

## Running
  Run 
      gratchk (sat|unsat) <cnf-file> <grat-file>

  The checker will print the line 
      s VERIFIED
  only if the formula provided in cnf-file is satisfiable/unsatisfiable.
