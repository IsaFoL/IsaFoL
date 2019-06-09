# default Isabelle path (the default is currently my home computer)
# you can use a command like
# make ISABELLE2018=<path/to/isabelle> ISABELLE=<path/to/isabelle> all
ISABELLE2017=/home/zmaths/Documents/isabelle/Isabelle2017
ISABELLE2018=/home/zmaths/Documents/isabelle/Isabelle2018
ISABELLE2019=/home/zmaths/Documents/isabelle/Isabelle2019-RC4
ISABELLE=/home/zmaths/Documents/isabelle/isabelle

# the concrete path to the isabelle executable
RUN_ISABELLE2017="$(ISABELLE2017)/bin/isabelle"
RUN_ISABELLE2018="$(ISABELLE2018)/bin/isabelle"
RUN_ISABELLE2019="$(ISABELLE2019)/bin/isabelle"
RUN_ISABELLE="$(ISABELLE)/bin/isabelle"

# destination of the documentation
ISABELLE2018_HOME=/home/zmaths/.isabelle/Isabelle2018/browser_info
ISABELLE2019_HOME=/home/zmaths/.isabelle/Isabelle2019-RC4/browser_info
ISABELLE_HOME=/home/zmaths/.isabelle/browser_info

# some more paths to extract the version
# TODO extract that from isabelle env
AFP=$(ISABELLE)/../afp-devel
DESTINATION="$(shell pwd)/html"

ISABELLE_version= $(shell (cd $(ISABELLE) && hg id --id))
AFP_version= $(shell (cd $(AFP) && hg id --id))
ISAFOL_version= $(shell (git log --pretty=format:'%h' -n 1))

AFP2018=$(ISABELLE2018)/../afp-2018
AFP2018_version= $(shell (cd $(AFP2018) && hg id --id))

AFP2019=$(ISABELLE2019)/../afp-2019
AFP2019_version= $(shell (cd $(AFP2019) && hg id --id))

test_vars:
	echo "Isabelle: $(ISABELLE_version)"
	echo "AFP: $(AFP_version)"
	echo "IsaFoL: $(ISAFOL_version)"

HOL:
	$(RUN_ISABELLE2018) build -b HOL

Weidenbach_Book:
	$(RUN_ISABELLE2019) build -d '$$AFP' -b Sepref_IICF
	$(RUN_ISABELLE2019) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Weidenbach_Book

Functional_Ordered_Resolution_Prover:
	$(RUN_ISABELLE2019) build -d '$$ISAFOR' -o browser_info -o "document=pdf" -v -b -D Functional_Ordered_Resolution_Prover

GRAT: HOL
	$(RUN_ISABELLE2017) build -d '$$AFP' -o browser_info -o "document=pdf" -v -b -D GRAT/gratchk

FOL_Berghofer: HOL
	$(RUN_ISABELLE2018) build -v -b -D FOL_Berghofer

Saturation_Framework:
	$(RUN_ISABELLE2018) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Saturation_Framework


all: Weidenbach_Book Ordered_Resolution_Prover GRAT FOL_Berghofer Saturation_Framework

# build the documentation and the files
current: Ordered_Resolution_Prover Functional_Ordered_Resolution_Prover
	$(RUN_ISABELLE2019) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -d Weidenbach_Book Full

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLE2019_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE2018_HOME)/Saturation_Framework $(DESTINATION)/current || :
	cp -R $(ISABELLE2019_HOME)/Functional_Ordered_Resolution_Prover $(DESTINATION)/current || :
	find $(DESTINATION)/current -name "*.html" -exec sed -i -e "s|(\* *\\\\htmllink{\(.*\)} *\*)|<a id=\"\1\"></a>|g" {} \;
	./add_dates.pl --noverbose --unsafe --isabelle="Isabelle2019" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFP2019_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
# We need the '|| true' since Isabelle can return a non-zero status for cleaning
# (because we do not rebuild the sesssions probably)
	$(RUN_ISABELLE2019) build -d '$$AFP' -c -n -D Weidenbach_Book || true
	$(RUN_ISABELLE2019) build -c -n -D FOL_Berghofer || true
	$(RUN_ISABELLE2019) build -d '$$AFP' -d '$$ISAFOR' -c -n -D Functional_Ordered_Resolution_Prover || true
	rm -rf $(DESTINATION)/current


.PHONY: Weidenbach_Book Ordered_Resolution_Prover Unordered_Resolution Functional_Ordered_Resolution_Prover Saturation_Framework
