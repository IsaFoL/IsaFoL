ISABELLE2016-1=/home/zmaths/Documents/isabelle/Isabelle2016-1
ISABELLE=/home/zmaths/Documents/isabelle/isabelle

RUN_ISABELLE="$(ISABELLE)/bin/isabelle"
RUN_ISABELLE2016-1="$(ISABELLE2016-1)/bin/isabelle"

ISABELLE_HOME=/home/zmaths/.isabelle/browser_info
ISABELLE2016-1_HOME=/home/zmaths/.isabelle/Isabelle2016-1/browser_info

AFP=$(ISABELLE)/../afp-devel
DESTINATION="$(shell pwd)/html"

ISABELLE_version= $(shell (cd $(ISABELLE) && hg id --id))
AFP_version= $(shell (cd $(AFP) && hg id --id))
ISAFOL_version= $(shell (git log --pretty=format:'%h' -n 1))


test_vars:
	echo "Isabelle: $(ISABELLE_version)"
	echo "AFP: $(AFP_version)"
	echo "IsaFoL: $(ISAFOL_version)"

HOL:
	$(RUN_ISABELLE) build -b HOL

Weidenbach_Book: HOL
	$(RUN_ISABELLE) build -d '$$AFP' -b Sepref_IICF
	$(RUN_ISABELLE) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Weidenbach_Book

Ordered_Resolution_Prover: HOL
	$(RUN_ISABELLE) build -d '$$AFP' -o browser_info -v -b -D Ordered_Resolution_Prover

Unordered_Resolution: HOL
	$(RUN_ISABELLE2016-1) build -o browser_info -v -b -D Unordered_Resolution

GRAT: HOL
	$(RUN_ISABELLE2016-1) build -d '$$AFP' -b Refine_Imperative_HOL
	$(RUN_ISABELLE2016-1) build -d '$$AFP' -o browser_info -o "document=pdf" -v -b -D GRAT/gratchk

FOL_Berghofer: HOL
	$(RUN_ISABELLE2016-1) build -v -b -D FOL_Berghofer

all: Weidenbach_Book Ordered_Resolution_Prover Unordered_Resolution GRAT FOL_Berghofer

# build the documentation and the files
current: Ordered_Resolution_Prover Unordered_Resolution
	$(RUN_ISABELLE) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -d Weidenbach_Book Full

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLE_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE_HOME)/Ordered_Resolution_Prover $(DESTINATION)/current || :
	cp -R $(ISABELLE2016-1_HOME)/Unsorted/Unordered_Resolution $(DESTINATION)/current || :
	./add_dates.pl --noverbose --unsafe --isabelle="$(ISABELLE_version)" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFP_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
	$(RUN_ISABELLE) build -d '$$AFP' -c -v -n -D Weidenbach_Book
	$(RUN_ISABELLE) build -c -v -n -D Ordered_Resolution_Prover
	$(RUN_ISABELLE2016-1) build -c -v -n -D Unordered_Resolution
	rm -rf $(DESTINATION)/current
