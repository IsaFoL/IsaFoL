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
    gratchk options
  where options are
    unsat <formula.cnf> <cert.grat>                 Check standard UNSAT certificate
    unsat <formula.cnf> <cert.gratl> <cert.gratp>   Check split UNSAT certificate
    sat <formula.cnf> <cert.lit>                    Check SAT certificate

  The checker will print the line 
      s VERIFIED
  only if the formula provided in cnf-file is satisfiable/unsatisfiable.
