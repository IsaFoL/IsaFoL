# default Isabelle path (the default is currently my home computer)
# you can use a command like
# make ISABELLE2018=<path/to/isabelle> ISABELLE=<path/to/isabelle> all
ISABELLERELEASE=/home/mathias/Documents/isabelle/Isabelle2025
ISABELLE=/home/mathias/Documents/isabelle/isabelle

# the concrete path to the isabelle executable
RUN_ISABELLERELEASE="$(ISABELLERELEASE)/bin/isabelle"
RUN_ISABELLE="$(ISABELLE)/bin/isabelle"

# destination of the documentation
ISABELLERELEASE_HOME=/home/mathias/.isabelle/Isabelle2025/browser_info
ISABELLE_HOME=/home/mathias/.isabelle/browser_info

# some more paths to extract the version
# TODO extract that from isabelle env
AFP=$(ISABELLE)/../afp-devel
DESTINATION="$(shell pwd)/html"

ISABELLE_version= $(shell (cd $(ISABELLE) && hg id --id))
ISABELLERELEASEversion= $(shell ($(RUN_ISABELLERELEASE) env | grep "ISABELLE_ID=" | sed "s|.*=\(.*\)$$|\1|g"))
AFP_version= $(shell (cd $(AFP) && hg id --id))
ISAFOL_version= $(shell (git log --pretty=format:'%h' -n 1))

AFPRELEASE=$(ISABELLERELEASE)/../afp-2025
AFPRELEASE_version=$(shell (cd $(AFPRELEASE) && hg id --id))

test_vars:
	echo "Isabelle: $(ISABELLERELEASE_version)"
	echo "AFP: $(AFPRELEASE_version)"
	echo "IsaFoL: $(ISAFOL_version)"

HOL:
	$(RUN_ISABELLERELEASE) build -b HOL

Weidenbach_Book:
	$(RUN_ISABELLERELEASE) build -d '$$AFP' -b Sepref_IICF
	$(RUN_ISABELLERELEASE) build -d '$$AFP' -d '$$ISABELLE_LLVM' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Weidenbach_Book

PAC:
	$(RUN_ISABELLERELEASE) build -d '$$AFP' -d '$$ISABELLE_LLVM' -d 'Weidenbach_Book' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D PAC_Checker2

GRAT: HOL
	$(RUN_ISABELLERELEASE) build -d '$$AFP' -o browser_info -o "document=pdf" -v -b -D GRAT/gratchk

FOL_Berghofer: HOL
	$(RUN_ISABELLERELEASE) build -j 4 -v -b -D FOL_Berghofer -D FOL_Monk -D Sequent_Calculus -D Simple_Prover

Unordered_Resolution: HOL
	$(RUN_ISABELLERELEASE) build -j 4 -v -d '$$AFP' -d '$$ISAFOR' -b -D Unordered_Resolution

all: Weidenbach_Book GRAT FOL_Berghofer Unordered_Resolution

# build the documentation and the files
current: Ordered_Resolution_Prover Functional_Ordered_Resolution_Prover

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLERELEASE_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLERELEASE_HOME)/PAC_Checker $(DESTINATION)/current || :
	find $(DESTINATION)/current -name "*.html" -exec sed -i -e "s|(\* *\\\\htmllink{\(.*\)} *\*)|<a id=\"\1\"></a>|g" {} \;
	./add_dates.pl --noverbose --unsafe --isabelle="Isabelle2025" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFPRELEASE_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
# We need the '|| true' since Isabelle can return a non-zero status for cleaning
# (because we do not rebuild the sesssions probably)
	$(RUN_ISABELLERELEASE) build -d '$$AFP' -d '$$ISABELLE_LLVM' -c -n -D Weidenbach_Book || true
	rm -rf $(DESTINATION)/current


.PHONY: Weidenbach_Book Ordered_Resolution_Prover Unordered_Resolution Functional_Ordered_Resolution_Prover PAC
