# A Comprehensive Framework for Saturation Theorem Proving #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Saturation_Framework/) contains a mechanization of a framework for formal refutational completeness proofs of abstract provers that implement saturation calculi.

Isabelle2019 is necessary to process the theory files.

## Authors of the mechanization ##

* framework: [Sophie Tourret](mailto:stourret mpi-inf.mpg.de)
* integration of superposition: [Simon Robillard](mailto:simon.robillard imt-atlantique.fr)
* integration of ordered resolution: [Sophie Tourret](mailto:stourret mpi-inf.mpg.de)

## Authors of the framework ##

* [Uwe Waldmann](mailto:uwe mpi-inf.mpg.de)
* [Sophie Tourret](mailto:stourret mpi-inf.mpg.de)
* [Simon Robillard](mailto:simon.robillard imt-atlantique.fr)
* [Jasmin Blanchette](mailto:j.c.blanchette vu.nl)

## Installation ##

Step 1. Download and install Isabelle2019:

Download and install Isabelle2018 as described on [http://isabelle.in.tum.de](http://isabelle.in.tum.de).  
Open Isabelle2019 (or more precisely Isabelle/jEdit using the command `<path_to_isabelle_folder>/bin/isabelle jedit`).  
If the "Isabelle build" window appears, then let it run until it disappears.  
Close the "Isabelle2019/HOL" window.  

Step 2. Download and install AFP-2019:

Download [afp-2019-08-19.tar.gz](https://sourceforge.net/projects/afp/files/afp-Isabelle2019/).  
Open the archive.  
Assuming you have downloaded your AFP directory to `/home/myself/afp`, you should run the following command (tested for Linux and Mac installations ‐ it should be the same under cygwin on Windows) to make the AFP session ROOTS available to Isabelle:

    echo "/home/myself/afp/thys" >> ~/.isabelle/Isabelle2019/ROOTS

Step 3. Download IsaFoL

    git clone https://bitbucket.org/isafol/isafol

Step 4. Open the theories:

Find `Saturation_Framework` in the IsaFoL folder.
It contains all the formalized results about the framework in the .thy files.
You can open any such file in Isabelle (for example using Isabelle/jEdit).

