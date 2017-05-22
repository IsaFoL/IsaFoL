# GRAT -- Efficient Formally Verified SAT Solver Certification Toolchain

GRAT is a SAT solver certificate checking tool chain, which is formally verified using the [Isabelle/HOL](https:/isabelle.in.tum.de) theorem prover.
If a certificate is verified, you have strong formal guarantees that the solution produced by the SAT solver was actually correct.

The tool chain consists of two programs: The unverified certificate generator <code>gratgen</code> converts a
DRAT certificate (as output by many modern SAT solvers) to a GRAT certificate, which is then checked against the original formula by the
verified <code>gratchk</code> tool.

## Features
* Strong formal correctness guarantees
* More than twice as fast as drat-trim thanks to novel heuristics (sepWL, RAT-run)
* Multi-threaded mode
* Small certificates thanks to backward checking and core-first unit propagation
* Memory efficient checking with split certificates

## News
* May 22, 2017: Version 1.2 released. New heuristics, now more than 2 times faster than drat-trim.

## Getting started
Download the [GRATgen](gratgen.tgz) and [GRATchk](gratchk.tgz) ([ML source only](gratchk-sml.tgz)) tools and build them as indicated in their README files.
The standard GRATchk package contains all Isabelle theories. However, to run the tools you only need the [ML source only](gratchk-sml.tgz) package.

To check a satisfiability certificate, run

    gratchk sat formula.cnf certificate.sat

Here, the formula is a formula in standard DIMACS CNF format, and the certificate is a list of non-contradictory literals that satisfy the formula if assigned to true.
The certificate can, for example, be obtained by processing the output of the SAT solver with

    sed -re '/^v/!d;s/^v//'

To check an unsatisfiability certificate, run

    gratgen formula.cnf drat-cert.drat -l grat-cert.gratl -o grat-cert.gratp [-j N]
    gratchk unsat formula.cnf grat-cert.gratl grat-cert.gratp

Here, drat-cert is a certificate in the standard DRAT format, which is supported by many SAT solvers. Note that the DRAT format is downward compatible with DRUP, such that also DRUP certificates can be used. Moreover, if you specify the -j N option, gratgen will run in multi-threaded mode with N threads.
For most certificates, this will result in a significant speedup. Good values for N are between 2 and 16, depending on the available hardware.

To check an unsatisfiability certificate in combined proof mode, i.e., lemmas and proofs are stored in the same file, run

    gratgen formula.cnf drat-cert.drat -o grat-cert.grat [-j N]
    gratchk unsat formula.cnf grat-cert.grat

Combined proof mode yields only a single certificate file, but the certificate checker is slightly slower and needs more memory.

### Examples
For getting started quickly, we have compiled a collection of [example formulas and certificates](examples.tgz).

## Benchmarks
We have benchmarked our checker (version 1.2) on a server board with an 22-core Intel XEON Broadwell 2.2GHz CPU and 128 GiB of RAM,
and compared it to drat-trim (version: Nov 10, 2016), the current version as of May 2017.
The benchmark set were the problems that CryptoMiniSAT solved in the [2016 SAT competition](http://baldur.iti.kit.edu/sat-competition-2016) main track.
We provide the raw csv files extracted from the logs: [sat.csv](sat.csv) [unsat.csv](unsat.csv).

Here are some numbers: In single-threaded mode, our tool chain successfully verifies all 110 unsatisfiable
problems in 82256 seconds, drat-trim needs 193217 seconds (2.3 times slower), including two timeouts at 20000 seconds and one SEGFAULT after 929 seconds.

Restricting the benchmark set to the 107 problems that drat-trim can verify, our tool chain needs 62455 seconds, while drat-trim needs 152288 seconds (2.4 times slower).

Using 8 threads, the wall-clock times of our tool chain sum up to only 29928 seconds (19740 seconds for the 107 drat-trim verifiable problems).

Note that our toolchain gives a result with strong formal correctness guarantees, while drat-trim is an unverified C program.

### Memory consumption
The increased speed and formal correctness guarantees come at the price of higher memory consumption. Our tool chain needs roughly twice the memory than drat-trim in single-threaded
mode, and memory consumption drastically increases in multi-threaded mode. However, memory consumption seems not to be a general problem.
In single-threaded mode, the maximum was roughly 11 GiB, with 8 threads, we required roughly 51 GiB.


## Documentation of the code
  GRATgen comes with a doxygen generated [documentation](gratgen-doc/index.html).
  For GRATchk, you may want to look at the [proof document](document.pdf) or the [proof outline](outline.pdf).


## Formal Guarantees
We have formally proved the soundness of GRATchk in the [Isabelle/HOL](https:/isabelle.in.tum.de) interactive theorem prover.
The proof covers the actual implementation of GRATchk, and the semantics of the formula down to the integer array that represents it.

That is, if GRATchk claims that a formula is satisfiable/unsatisfiable, it is very likely that this is actually true.

### Trusted Base
The trusted base of a piece of software describes what has to be trusted in order to believe that the produced result is correct.
It includes, at least, the hardware, the operating system, and the compilers used to compile the software.

For a SAT solver, it includes the complete implementation of a SAT solver, usually a highly optimized C program.
If one uses certificates, the sat solver is replaced by the certificate checker in the trusted base.

For formally verified software, the software itself is not included in the trusted base any more.
It is replaced by the trusted base of the used theorem prover and by the correctness specification.
This highly decreases the likelihood of bugs in the verified software:

 * Modern theorem provers like Isabelle/HOL are designed for maximum trustworthiness, reducing their own trusted base to a small and well-tested logical kernel.
 * It is very unlikely that a bug in the logical kernel coincides with an error in the correctness proof.

We now list, in detail, the trusted code base of our verified checker, i.e., what pieces of software you have to trust in order to believe in correctness of our checker:

 * The Isabelle/HOL logical inference kernel. This piece of code is considerably small and very well tested. In the last decade, we discovered less than 5 bugs,
  **none of them** leading to an inconsistent theorem being proved unnoticed!

 * The Isabelle/HOL code generator and its Imperative HOL extension. The code generator is merely a syntax transformation from the
  functional fragment of HOL to the target language, in our case Standard ML. It's correctness has been proved on paper, and it is well-tested.
  Again, it is unlikely that an error in code generation will result in the verified checker accepting an invalid certificate.
  It is much more likely that the checker will just not compile, or fail with an exception at runtime.

 * The correctness theorem that we proved for the certified checker. In particular, you have to believe that the correctness theorem specifies the desired behavior of the checker.
  To this end, we provide a specification of a satisfying formula down to the integer array that holds null-terminated clauses of the formula, only using standard list functions.
  Excluding the definitions of the standard list functions, this specification is only a few lines of Isabelle/HOL source text.
  See the last section of the [proof outline](outline.pdf) for a detailed explanation.

 * A small parser that parses the cnf file into an integer array. We tried to write this parser as clear as possible.
  Moreover, using Standard ML, it is immune to low-level bugs like numeric or buffer overflows.

 * The small piece of code that interprets the command line, invokes the parser and the generated code of the verifier, and prints the result.


While this list may seem huge, it is worth to list some items that are missing as opposed to an unverified checker written in C:

 * That there are no buffer overflows of any kind.
 * Correctness of the used data structures. This includes a map from clause IDs to clauses, from literals to their assignments,
  the management of RAT candidates, and that all code using these data structures satisfies their (often undocumented) preconditions.
 * Correctness of RUP and RAT checks per se, as well as unit propagation.
 * Correctness of the implementation of these concepts using partial assignments.
 * Correctness of the implementation of overall proof checking, e.g., that all lemmas are checked at the end.


## Version History
  * [Version 1.0](archive/v1.0/index.html) Initial version of GRAT
  * [Version 1.1](archive/v1.1/index.html)
    * Summarized deletion items
    * Split certificates

### Version 1.2 (Current) ###
  * Separate watchlists (sepWL): More efficient implementation of core-first unit propagation.
  * RAT-run heuristics: Reduction of expensive RAT candidate queries.

