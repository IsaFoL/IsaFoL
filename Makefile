ISABELLE2016=~/isabelle/Isabelle2016/bin/isabelle
ISABELLE=~/isabelle/isabelle/bin/isabelle

ISABELLE_HOME=~/.isabelle/browser_info
ISABELLE2016_HOME=~/.isabelle/Isabelle2016/browser_info

DESTINATION=./html

all: current

# build the documentation and the files
current:
	$(ISABELLE) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -d Weidenbach_Book Full
	$(ISABELLE) build -o browser_info -v -D Bachmair_Ganzinger
	$(ISABELLE2016) build -o browser_info -v -D Unordered_Resolution


# need to be in the IJCAR branch
conference:
	$(ISABELLE2016) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -D Weidenbach_Book
	cp -R $(ISABELLE2016_HOME)/Unsorted/Weidenbach_Book $(DESTINATION)/IJCAR2016 || :

	$(ISABELLE2016) build -o browser_info -v -D Bachmair_Ganzinger
	cp -R $(ISABELLE2016_HOME)/Unsorted/Bachmair_Ganzinger $(DESTINATION)/IJCAR2016 || :

# move the html documentation to the locale directory
doc:
	cp -R $(ISABELLE_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE_HOME)/Bachmair_Ganzinger $(DESTINATION)/current || :
	cp -R $(ISABELLE2016_HOME)/Unsorted/Unordered_Resolution $(DESTINATION)/current || :

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
	$(ISABELLE) build -c -v -D Weidenbach_Book
	$(ISABELLE) build -c -v -D Bachmair_Ganzinger
	$(ISABELLE2016) build -c -v -D Unordered_Resolution