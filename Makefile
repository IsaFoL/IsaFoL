ISABELLE2016=~/isabelle/Isabelle2016
ISABELLE=~/isabelle/isabelle

RUN_ISABELLE="$(ISABELLE)/bin/isabelle"
RUN_ISABELLE2016="$(ISABELLE2016)/bin/isabelle"

ISABELLE_HOME=~/.isabelle/browser_info
ISABELLE2016_HOME=~/.isabelle/Isabelle2016/browser_info

AFP=$(ISABELLE)/../afp-devel
DESTINATION="$(shell pwd)/html"

ISABELLE_version= $(shell (cd $(ISABELLE) && hg id --id))
AFP_version= $(shell (cd $(AFP) && hg id --id))
ISAFOL_version= $(shell (git log --pretty=format:'%h' -n 1))

test_vars:
	echo "Isabelle: $(ISABELLE_version)"
	echo "AFP: $(AFP_version)"
	echo "IsaFoL: $(ISAFOL_version)"

all:
	$(RUN_ISABELLE) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -D Weidenbach_Book
	$(RUN_ISABELLE) build -o browser_info -v -D Bachmair_Ganzinger
	$(RUN_ISABELLE) build -o browser_info -v -D Unordered_Resolution

# build the documentation and the files
current:
	$(RUN_ISABELLE) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -d Weidenbach_Book Full
	$(RUN_ISABELLE) build -o browser_info -v -D Bachmair_Ganzinger
	$(RUN_ISABELLE2016) build -o browser_info -v -D Unordered_Resolution

# need to be in the IJCAR branch
conference:
	$(RUN_ISABELLE2016) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -D Weidenbach_Book
	cp -R $(ISABELLE2016_HOME)/Unsorted/Weidenbach_Book $(DESTINATION)/IJCAR2016 || :

	$(RUN_ISABELLE2016) build -o browser_info -v -D Bachmair_Ganzinger
	cp -R $(ISABELLE2016_HOME)/Unsorted/Bachmair_Ganzinger $(DESTINATION)/IJCAR2016 || :

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLE_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE_HOME)/Bachmair_Ganzinger $(DESTINATION)/current || :
	cp -R $(ISABELLE2016_HOME)/Unsorted/Unordered_Resolution $(DESTINATION)/current || :
	./add_dates.pl --noverbose --unsafe --isabelle="$(ISABELLE_version)" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFP_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
	$(RUN_ISABELLE) build -c -v -D Weidenbach_Book
	$(RUN_ISABELLE) build -c -v -D Bachmair_Ganzinger
	$(RUN_ISABELLE2016) build -c -v -D Unordered_Resolution
	rm -rf $(DESTINATION)/current