TEX=root

# You probably don't need to change anything below the following line:
.PHONY: clean ps pdf dvi holbib clean check clean_snippets
LATEX_ARGS= --interaction batchmode

all: check $(TEX).pdf


check:
	@egrep --color --file error_patterns *.tex --exclude macros.tex --exclude lstisabelle.tex; true
	@for i in *.tex; do \
	  o=`cat $$i | sed -re 's/(\\\\(ref|label|input)|label=)\\{[^\\}]*}//g' | egrep -v "^[ \t]*%" | egrep -o "[[:alpha:]]+-[[:alpha:]-]+" | tr "[:upper:]" "[:lower:]" | sort -u | egrep -v --file allow_hyphen`; \
	  test -n "$$o" && echo "$$i:" $$o | egrep --color "^.*:"; \
	done; true
#	egrep -o "[[:alpha:]]+-[[:alpha:]-]+" *.tex | tr "[:upper:]" "[:lower:]" | sed -re "s/:/: /g" | sort -k2 -u | egrep -v --file allow_hyphen | sort | egrep --color "[[:alpha:]]+-[[:alpha:]-]+"; true

# Note: Diabled, until we have solution how to build snippets and document
#snippets/snippets.tex:
#	isabelle build -d ../formalization Snippets && cp ../formalization/generated/snippets.tex snippets/snippets.tex

snippets/snippets.out.tex: snippets/snippets.tex massage_snippets.sed
	sed -rf massage_snippets.sed snippets/snippets.tex > snippets/snippets.out.tex

$(TEX).pdf: *.tex snippets/snippets.out.tex *.bib
	latexmk -pdf $(TEX).tex; err=$$?; egrep --color -i 'error|warning|overfull|underfull|undef|^l\.[0-9]' $(TEX).log; grep --color=never "Output written" $(TEX).log; exit $$err

clean:
	@rm -f *.toc *.aux *.dvi *.log *.lof *.bbl *.blg *.hix *.tid *.tde *~ snippets/*.out.tex

#clean_snippets: clean
#	@rm -rf snippets/*.tex
