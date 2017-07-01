# Formalization of First-Order Unordered Resolution #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Unordered_Resolution/) contains an Isabelle formalization of unordered resolution for first-order logic. It has been [moved to the Archive of Formal Proofs](https://www.isa-afp.org/entries/Resolution_FOL.shtml). The only exception is a formal proof of the unification theorem. It is proved here by loading it from a theory in the [IsaFoR project](http://cl-informatik.uibk.ac.at/software/ceta/) and doing conversions between the terms of the two theories. The assumption in the unification locale can then be instantiated, and we obtain the completeness theorem from the locale.

## Author ##

* [Anders Schlichtkrull](mailto:andschl shtrudel dtu.dk)

## Inspired by [work](http://afp.sourceforge.net/entries/FOL-Fitting.shtml) of ##

* [Stefan Berghofer](mailto:berghofe shtrudel in.tum.de)

## News: Additional Completeness results ##
I have proven some additional completeness results. They are available at the end of [this file](https://bitbucket.org/isafol/isafol/src/unordered_jar/Unordered_Resolution/Resolution_FOL/Completeness.thy) following the theorem named completeness. I plan to add them to the AFP entry.

## Installation ##
* [Download and install Isabelle2016-1](https://isabelle.in.tum.de)
* [Download AFP version afp-2016-12-17](https://sourceforge.net/projects/afp/files/afp-Isabelle2016-1/)
* [Install it in Isabelle](https://www.isa-afp.org/using.shtml)
* [Download IsaFoR/CeTA - the development version with changeset d836ee46a5ed](http://cl2-informatik.uibk.ac.at/rewriting/mercurial.cgi/IsaFoR/archive/d836ee46a5ed.tar.bz2)
* Extract it to get a folder called `-CeTA-657d09abd9ab`.
* Install IsaFoR in Isabelle by adding `/full/path/to/-CeTA-657d09abd9ab` to `~/.isabelle/Isabelle2016/etc/components`.
* Download and open the theories in this project.

## In Archive of Formal Proofs ##

* [The Resolution Calculus for First-Order Logic](https://www.isa-afp.org/entries/Resolution_FOL.shtml)
  A. Schlichtkrull.
  Archive of Formal Proofs, Formal proof development

## Publications ##

* [Formalization of the Resolution Calculus for First-Order Logic](http://orbit.dtu.dk/files/126069253/typeinst.pdf).
  A. Schlichtkrull.
  In Blanchette, J. C., Merz, S. (eds.) 7th International Conference on Interactive Theorem Proving (ITP 2016), LNCS 9807, Springer, 2016.

* [Meta-Logical Reasoning in Higher-Order Logic](http://orbit.dtu.dk/files/118776437/logica_poster.pdf).
  J. Villadsen, A. Schlichtkrull, and A. V. Hess.
  Poster session presented at 29th Annual International Symposia Devoted to Logic (LOGICA 2015), 2015.

* [Formalization of Resolution Calculus in Isabelle](http://people.compute.dtu.dk/andschl/Thesis.pdf).
  A. Schlichtkrull.
  M.Sc. thesis, Technical University of Denmark, 2015.
