# A Comprehensive Framework for Saturation Theorem Proving #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Saturation_Framework/) contains a mechanization of a framework for formal refutational completeness proofs of abstract provers that implement saturation calculi.
[This paper](http://matryoshka.gforge.inria.fr/pubs/saturate_paper.pdf) and [this technical report](http://matryoshka.gforge.inria.fr/pubs/saturate_report.pdf) explain the theory behind it.

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

Download and install Isabelle2019 as described on [http://isabelle.in.tum.de](http://isabelle.in.tum.de).  
Open Isabelle2019 (or more precisely Isabelle/jEdit using the command `<path_to_isabelle_folder>/bin/isabelle jedit`).  
If the "Isabelle build" window appears, then let it run until it disappears.  
Close the "Isabelle2019/HOL" window.  

Step 2. Download and install AFP-2019:

Download [afp-2019-08-19.tar.gz](https://sourceforge.net/projects/afp/files/afp-Isabelle2019/).  
Open the archive.  
Assuming you have downloaded your AFP directory to `/home/myself/afp`, you should run the following command (tested for Linux and Mac installations ‐ it should be the same under cygwin on Windows) to make the AFP session ROOTS available to Isabelle:

    echo "/home/myself/afp/thys" >> ~/.isabelle/Isabelle2019/ROOTS

Step 3. Download IsaFoL:

    git clone https://bitbucket.org/isafol/isafol

Step 4. Open the theories:

Find `Saturation_Framework` in the IsaFoL folder.
It contains all the formalized results about the framework in the .thy files.
You can open any such file in Isabelle (for example using Isabelle/jEdit).

## Where to find what ##

The results in the paper and technical report can be found in the following files:

* Definitions about consequence relations and inference systems (Sect. 2) are in `Consequence_Relations_and_Inference_Systems.thy`
* Results about refutational completeness and intersection of redundancy criteria (Sect. 2) are in `Calculi.thy`
* Results about standard lifting, well-founded orderings and intersection of liftings (Sect. 3) are in `Lifting_to_Non_Ground_Calculi.thy`
* Results regarding the addition of labels (Sect. 3) are in `Labeled_Lifting_to_Non_Ground_Calculi.thy`
* Results regarding the Given Clause prover architecture (Sect. 4) are in `Prover_Architectures.thy`

In addition, the results in the technical report are annotated in the margin with the same labels as in the .thy files.
The formalization of Sect. 4 is still ongoing. In particular, the Otter and DISCOUNT loops are not yet formalized.


