TMP=tmp
REPORT=paper
BIBDEPS=splncs04.bst paper.bib
DEPS=paper.tex paper.bib appendix.tex splncs04.bst llncs.cls

$(REPORT).pdf: $(DEPS)
	mkdir -p $(TMP)
	pdflatex -output-directory $(TMP) $(REPORT).tex
	cp $(BIBDEPS) $(TMP) && cd $(TMP) && bibtex $(REPORT).aux
	pdflatex -output-directory $(TMP) $(REPORT).tex
	pdflatex -output-directory $(TMP) $(REPORT).tex
	mv $(TMP)/$(REPORT).pdf .

clean:
	rm -r $(TMP)
