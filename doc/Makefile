MAIN = {main,pts}

all: pts.pdf main.pdf

%.pdf: $(wildcard *.tex) %.bib
	pdflatex $(@:.pdf=.tex)
	bibtex $(@:.pdf=)
	pdflatex $(@:.pdf=.tex)
	pdflatex $(@:.pdf=.tex)

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).synctex.gz $(MAIN).blg texput.log

distclean: clean
	rm -f $(MAIN).pdf $(MAIN).bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg

.PHONY: all clean distclean
