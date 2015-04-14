MAIN = pts

all: $(MAIN).pdf

%.pdf: %.tex %.bib
	pdflatex $(@:.pdf=.tex)
	bibtex $(@:.pdf=)
	pdflatex $(@:.pdf=.tex)
	pdflatex $(@:.pdf=.tex)

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).synctex.gz $(MAIN).blg texput.log

distclean: clean
	rm -f $(MAIN).pdf $(MAIN).bbl *.aux *.out *.synctex.gz *.log *.fdb_latexmk *.blg

.PHONY: all clean distclean
