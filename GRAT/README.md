# GRAT SAT Solver Verification Toolchain #

GRAT is a SAT solver certificate checking tool chain, which is formally verified using the
[Isabelle/HOL](https:/isabelle.in.tum.de) proof assistant. If a certificate is verified, you have
strong formal guarantees that the solution produced by the SAT solver was actually correct.

The tool chain consists of two programs: The unverified certificate generator <code>gratgen</code>
converts a DRAT certificate (as output by many modern SAT solvers) to a GRAT certificate, which is
then checked against the original formula by the verified <code>gratchk</code> tool.

## Features ##

* Strong formal correctness guarantees
* Single-threaded mode: As fast as the standard tool DRAT-trim
* Multi-threaded mode: Up to nine times faster
* Small certificates thanks to backward checking and core-first unit propagation

## Author ##

* [Peter Lammich](mailto:lammich shtrudel in.tum.de)
