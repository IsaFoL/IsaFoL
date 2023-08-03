# default Isabelle path (the default is currently my home computer)
# you can use a command like
# make ISABELLE2018=<path/to/isabelle> ISABELLE=<path/to/isabelle> all
ISABELLE2022=/home/mathias/Documents/isabelle/Isabelle2022
ISABELLE2023=/home/mathias/Documents/isabelle/Isabelle2023
ISABELLE=/home/mathias/Documents/isabelle/isabelle

# the concrete path to the isabelle executable
RUN_ISABELLE2023="$(ISABELLE2023)/bin/isabelle"
RUN_ISABELLE="$(ISABELLE)/bin/isabelle"

# destination of the documentation
ISABELLE2022_HOME=/home/mathias/.isabelle/Isabelle2022/browser_info
ISABELLE2023_HOME=/home/mathias/.isabelle/Isabelle2023-RC2/browser_info
ISABELLE_HOME=/home/mathias/.isabelle/browser_info

# some more paths to extract the version
# TODO extract that from isabelle env
AFP=$(ISABELLE)/../afp-devel
DESTINATION="$(shell pwd)/html"

ISABELLE_version= $(shell (cd $(ISABELLE) && hg id --id))
ISABELLE2023_version= $(shell ($(RUN_ISABELLE2023) env | grep "ISABELLE_ID=" | sed "s|.*=\(.*\)$$|\1|g"))
AFP_version= $(shell (cd $(AFP) && hg id --id))
ISAFOL_version= $(shell (git log --pretty=format:'%h' -n 1))

AFP2022=$(ISABELLE2022)/../afp-2022
AFP2022_version=$(shell (cd $(AFP2022) && hg id --id))

AFP2023=$(ISABELLE2023)/../afp-2023
AFP2023_version=$(shell (cd $(AFP2023) && hg id --id))

test_vars:
	echo "Isabelle: $(ISABELLE2023_version)"
	echo "AFP: $(AFP2023_version)"
	echo "IsaFoL: $(ISAFOL_version)"

HOL:
	$(RUN_ISABELLE2023) build -b HOL

Weidenbach_Book:
	$(RUN_ISABELLE2023) build -d '$$AFP' -b Sepref_IICF
	$(RUN_ISABELLE2023) build -d '$$AFP' -d '$$ISABELLE_LLVM' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Weidenbach_Book

PAC:
	$(RUN_ISABELLE2023) build -d '$$AFP' -d '$$ISABELLE_LLVM' -d 'Weidenbach_Book' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D PAC_Checker2

GRAT: HOL
	$(RUN_ISABELLE2023) build -d '$$AFP' -o browser_info -o "document=pdf" -v -b -D GRAT/gratchk

FOL_Berghofer: HOL
	$(RUN_ISABELLE2023) build -j 4 -v -b -D FOL_Berghofer -D FOL_Monk -D Sequent_Calculus -D Simple_Prover

Unordered_Resolution: HOL
	$(RUN_ISABELLE2023) build -j 4 -v -d '$$AFP' -d '$$ISAFOR' -b -D Unordered_Resolution

all: Weidenbach_Book GRAT FOL_Berghofer Unordered_Resolution

# build the documentation and the files
current: Ordered_Resolution_Prover Functional_Ordered_Resolution_Prover

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLE2022_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE2022_HOME)/PAC_Checker $(DESTINATION)/current || :
	find $(DESTINATION)/current -name "*.html" -exec sed -i -e "s|(\* *\\\\htmllink{\(.*\)} *\*)|<a id=\"\1\"></a>|g" {} \;
	./add_dates.pl --noverbose --unsafe --isabelle="Isabelle2022" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFP2022_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
# We need the '|| true' since Isabelle can return a non-zero status for cleaning
# (because we do not rebuild the sesssions probably)
	$(RUN_ISABELLE2023) build -d '$$AFP' -d '$$ISABELLE_LLVM' -c -n -D Weidenbach_Book || true
	rm -rf $(DESTINATION)/current


.PHONY: Weidenbach_Book Ordered_Resolution_Prover Unordered_Resolution Functional_Ordered_Resolution_Prover PAC
