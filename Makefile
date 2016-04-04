ISABELLE2016=/home/zmaths/isabelle/Isabelle2016/bin/isabelle
ISABELLE=/home/zmaths/isabelle/isabelle/bin/isabelle

ISABELLE_HOME=/home/zmaths/.isabelle/browser_info
ISABELLE2016_HOME=/home/zmaths/.isabelle/Isabelle2016/browser_info

DESTINATION=/home/zmaths/ENS/isafol/html

all: current


current:
	$(ISABELLE) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -D Weidenbach_Book
	cp -R $(ISABELLE_HOME)/Weidenbach_Book $(DESTINATION)/current

	$(ISABELLE) build -o browser_info -v -D Bachmair_Ganzinger
	cp -R $(ISABELLE_HOME)/Bachmair_Ganzinger $(DESTINATION)/current

	$(ISABELLE2016) build -o browser_info -v -D Unordered_Resolution
	cp -R $(ISABELLE2016_HOME)/Unsorted/Unordered_Resolution $(DESTINATION)/current

conference:
	$(ISABELLE2016) build -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -D Weidenbach_Book
	cp -R $(ISABELLE2016_HOME)/Unsorted/Weidenbach_Book $(DESTINATION)/IJCAR2016

	$(ISABELLE2016) build -o browser_info -v -D Bachmair_Ganzinger
	cp -R $(ISABELLE2016_HOME)/Unsorted/Bachmair_Ganzinger $(DESTINATION)/IJCAR2016

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
	$(ISABELLE) build -c -v -D Weidenbach_Book
	$(ISABELLE) build -c -v -D Bachmair_Ganzinger
	$(ISABELLE2016) build -c -v -D Unordered_Resolution