# GRAT SAT Solver Verification Toolchain #

GRAT is a SAT solver certificate checking tool chain, which is formally verified using the
[Isabelle/HOL](https:/isabelle.in.tum.de) proof assistant. If a certificate is verified, you have
strong formal guarantees that the solution produced by the SAT solver was actually correct.

The tool chain consists of two programs: The unverified certificate generator <code>gratgen</code>
converts a DRAT certificate (as output by many modern SAT solvers) to a GRAT certificate, which is
then checked against the original formula by the verified <code>gratchk</code> tool.


## Getting Started ##

See index.md.


## Features ##

* Strong formal correctness guarantees
* More than twice as fast as drat-trim thanks to novel heuristics (sepWL, RAT-run)
* Multi-threaded mode
* Small certificates thanks to backward checking and core-first unit propagation
* Memory efficient checking with split certificates


## News ##
### Version 1.1 ###
  * Support for split certificates

### Version 1.2 ###
  * Separate watchlists (sepWL): More efficient implementation of core-first unit propagation.
  * RAT-run heuristics: Reduction of expensive RAT candidate queries.

### Version 1.3 ###
  * Binary drat format

## Author ##

* [Peter Lammich](mailto:lammich shtrudel in.tum.de)
