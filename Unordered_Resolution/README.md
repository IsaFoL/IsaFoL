# Formalization of First-Order Unordered Resolution #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Unordered_Resolution/) used to contain an Isabelle formalization of unordered resolution for first-order logic. The formalization has been [moved to the Archive of Formal Proofs](https://www.isa-afp.org/entries/Resolution_FOL.shtml). 
From AFP version 2018 and forward this includes a formal proof of the unification theorem. It is proved here by loading theories from the [First_Order_Terms entry](https://www.isa-afp.org/entries/First_Order_Terms.html) and doing conversions between two entries' definitions of terms. The assumption in the unification locale is then instantiated, and we obtain the completeness theorem from the locale.


## Author ##

* [Anders Schlichtkrull](mailto:andschl shtrudel dtu.dk)


## Inspired by [work](http://afp.sourceforge.net/entries/FOL-Fitting.shtml) of ##

* [Stefan Berghofer](mailto:berghofe shtrudel in.tum.de)


## Additional Completeness Results ##

For the JAR paper I proved some additional completeness results compared to the ITP paper. 
They are available the AFP entry from version 2018 and forward.


## Installation ##

* [Download and install the newest version of Isabelle](https://isabelle.in.tum.de)
* [Install AFP](https://www.isa-afp.org/using.html)
* Open theories in '/path/to/AFP/Resolution/Resolution_FOL'

Alternatively you can just install Isabelle without AFP, and then download
[the Resolution_FOL entry](https://www.isa-afp.org/entries/Resolution_FOL.html).
All theories will load except 'Unification_Theorem.thy' and 'Completeness_Instance.thy'
which rely on AFP being installed.


## Entry in the Archive of Formal Proofs ##

* [The Resolution Calculus for First-Order Logic](https://www.isa-afp.org/entries/Resolution_FOL.shtml)
  A. Schlichtkrull.
  Archive of Formal Proofs, Formal proof development.


## Publications ##

* [Formalization of the Resolution Calculus for First-Order Logic](https://people.compute.dtu.dk/andschl/#jar).
  A. Schlichtkrull.
  _Journal of Automated Reasoning_, 2018.
  
* [Formalization of the Resolution Calculus for First-Order Logic](http://orbit.dtu.dk/files/126069253/typeinst.pdf).
  A. Schlichtkrull.
  In Blanchette, J. C., Merz, S. (eds.) 7th International Conference on Interactive Theorem Proving (ITP 2016), LNCS 9807, Springer, 2016.

* [Meta-Logical Reasoning in Higher-Order Logic](http://orbit.dtu.dk/files/118776437/logica_poster.pdf).
  J. Villadsen, A. Schlichtkrull, and A. V. Hess.
  Poster session presented at 29th Annual International Symposia Devoted to Logic (LOGICA 2015), 2015.

* [Formalization of Resolution Calculus in Isabelle](http://people.compute.dtu.dk/andschl/Thesis.pdf).
  A. Schlichtkrull.
  M.Sc. thesis, Technical University of Denmark, 2015.
