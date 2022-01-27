# default Isabelle path (the default is currently my home computer)
# you can use a command like
# make ISABELLE2018=<path/to/isabelle> ISABELLE=<path/to/isabelle> all
ISABELLE2017=/home/zmaths/Documents/isabelle/Isabelle2017
ISABELLE2018=/home/zmaths/Documents/isabelle/Isabelle2018
ISABELLE2019=/home/zmaths/Documents/isabelle/Isabelle2019
ISABELLE2020=/home/zmaths/Documents/isabelle/Isabelle2020
ISABELLE2021=/home/zmaths/Documents/isabelle/Isabelle2021
ISABELLE20211=/home/zmaths/Documents/isabelle/Isabelle2021-1
ISABELLE=/home/zmaths/Documents/isabelle/isabelle

# the concrete path to the isabelle executable
RUN_ISABELLE2017="$(ISABELLE2017)/bin/isabelle"
RUN_ISABELLE2018="$(ISABELLE2018)/bin/isabelle"
RUN_ISABELLE2019="$(ISABELLE2019)/bin/isabelle"
RUN_ISABELLE2020="$(ISABELLE2020)/bin/isabelle"
RUN_ISABELLE2021="$(ISABELLE2021)/bin/isabelle"
RUN_ISABELLE20211="$(ISABELLE20211)/bin/isabelle"
RUN_ISABELLE="$(ISABELLE)/bin/isabelle"

# destination of the documentation
ISABELLE2018_HOME=/home/zmaths/.isabelle/Isabelle2018/browser_info
ISABELLE2019_HOME=/home/zmaths/.isabelle/Isabelle2019/browser_info
ISABELLE2020_HOME=/home/zmaths/.isabelle/Isabelle2020/browser_info
ISABELLE2021_HOME=/home/zmaths/.isabelle/Isabelle2021/browser_info
ISABELLE20211_HOME=/home/zmaths/.isabelle/Isabelle2021-1/browser_info
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

AFP2020=$(ISABELLE2020)/../afp-2020
AFP2020_version=$(shell (cd $(AFP2020) && hg id --id))

AFP2021=$(ISABELLE2021)/../afp-2021
AFP2021_version=$(shell (cd $(AFP2021) && hg id --id))

AFP20211=$(ISABELLE2021-1)/../afp-2021-1
AFP20211_version=$(shell (cd $(AFP2021-1) && hg id --id))

test_vars:
	echo "Isabelle: $(ISABELLE_version)"
	echo "AFP: $(AFP_version)"
	echo "IsaFoL: $(ISAFOL_version)"

HOL:
	$(RUN_ISABELLE20211) build -b HOL

Weidenbach_Book:
	$(RUN_ISABELLE20211) build -d '$$AFP' -b Sepref_IICF
	$(RUN_ISABELLE20211) build -d '$$AFP' -d '$$ISABELLE_LLVM' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D Weidenbach_Book

PAC:
	$(RUN_ISABELLE20211) build -d '$$AFP' -d '$$ISABELLE_LLVM' -d 'Weidenbach_Book' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -D PAC_Checker2

Functional_Ordered_Resolution_Prover:
	$(RUN_ISABELLE2019) build -d '$$ISAFOR' -o browser_info -o "document=pdf" -v -b -D Functional_Ordered_Resolution_Prover

GRAT: HOL
	$(RUN_ISABELLE2017) build -d '$$AFP' -o browser_info -o "document=pdf" -v -b -D GRAT/gratchk

FOL_Berghofer: HOL
	$(RUN_ISABELLE20211) build -j 4 -v -b -D FOL_Berghofer -D FOL_Monk -D Sequent_Calculus -D Simple_Prover

all: Weidenbach_Book Ordered_Resolution_Prover GRAT FOL_Berghofer Saturation_Framework

# build the documentation and the files
current: Ordered_Resolution_Prover Functional_Ordered_Resolution_Prover
	$(RUN_ISABELLE2019) build -d '$$AFP' -o browser_info -o "document=pdf" -o "document_variants=document:outline=/proof,/ML;userguide" -v -b -d Weidenbach_Book Full

# move the html documentation to the locale directory
doc:
	mkdir -p $(DESTINATION)/current
	cp -R $(ISABELLE20211_HOME)/Weidenbach_Book $(DESTINATION)/current || :
	cp -R $(ISABELLE20211_HOME)/PAC_Checker $(DESTINATION)/current || :
	find $(DESTINATION)/current -name "*.html" -exec sed -i -e "s|(\* *\\\\htmllink{\(.*\)} *\*)|<a id=\"\1\"></a>|g" {} \;
	./add_dates.pl --noverbose --unsafe --isabelle="Isabelle2021-1" --isafol="$(ISAFOL_version)" --html="$(DESTINATION)/current" --afp="$(AFP2021_version)"

refs:
	../isafol-private/Other/update_refs.pl  --unsafe

clean:
# We need the '|| true' since Isabelle can return a non-zero status for cleaning
# (because we do not rebuild the sesssions probably)
	$(RUN_ISABELLE20211) build -d '$$AFP' -d '$$ISABELLE_LLVM' -c -n -D Weidenbach_Book || true
	rm -rf $(DESTINATION)/current


.PHONY: Weidenbach_Book Ordered_Resolution_Prover Unordered_Resolution Functional_Ordered_Resolution_Prover Saturation_Framework PAC
