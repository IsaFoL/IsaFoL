# A Verified Functional Implementation of Bachmair and Ganzinger's Ordered Resolution Prover #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Functional_Ordered_Resolution_Prover/) contains the verified RPx prover which is a refinement of the specification of an ordered resolution prover presented in Section 4.3 of Bachmair and Ganzinger's "Resolution Theorem Proving" (Chapter 2 of Volume 1 of _The Handbook of Automated Reasoning_).

Isabelle2018 is necessary to process the theory files.

## Organization of the Development ##

* The branch [master](https://bitbucket.org/isafol/isafol/src/master/Functional_Ordered_Resolution_Prover/) contains the latest development.
* The branch [CPP2019](https://bitbucket.org/isafol/isafol/src/CPP2019/Functional_Ordered_Resolution_Prover/) contains the version of the development as of the submission of our CPP2019 paper.


## Authors ##

* [Anders Schlichtkrull](mailto:anders shtrudel dtu.dk)
* [Jasmin Christian Blanchette](mailto:jasmin.blanchette shtrudel inria.fr)
* [Dmitriy Traytel](mailto:traytel shtrudel inf.ethz.ch)


## Installation ##

Step 1. Download and install Isabelle2018:

Download and install Isabelle2018 as described on [http://isabelle.in.tum.de](http://isabelle.in.tum.de).  
Open Isabelle2018 (or more precisely Isabelle/jEdit).  
If the "Isabelle build" window appears, then let it run until it disappears.  
Close the "Isabelle2018/HOL" window.  


Step 2. Download and install AFP-2018:

    ~/RPx $ hg clone https://bitbucket.org/isa-afp/afp-2018 -r 96e565d
    ~/RPx $ cd afp-2018
    ~/RPx/afp-devel $ pwd >> ~/.isabelle/Isabelle2018/etc/components
    ~/RPx/afp-devel $ cd ..


Step 3. Download and install the IsaFoR repository version `db6a3973b702`:

    ~/RPx $ hg clone http://cl2-informatik.uibk.ac.at/rewriting/mercurial.cgi/IsaFoR -r db6a3973b702
    ~/RPx $ cd IsaFoR/thys
    ~/RPx/IsaFoR/thys $ pwd >> ~/.isabelle/Isabelle2018/ROOTS
    ~/RPx/IsaFoR/thys $ cd ../..
    
Step 4. Download IsaFoL

    ~/RPx $ git clone https://bitbucket.org/isafol/isafol

Step 4. Open the theories:

Find Functional_Ordered_Resolution_Prover/Executable_FO_Ordered_Resolution_Prover.thy in the isafol 
folder and open it in Isabelle (or more precisely Isabelle/jEdit). Consider in particular the theorem 
prover_complete_refutation. You can also inspect the other .thy files.
