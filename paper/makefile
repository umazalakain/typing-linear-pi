TMP=tmp
REPORT=paper

paper.pdf: $(REPORT).tex $(REPORT).bib appendix.tex
	mkdir -p $(TMP)
	pdflatex -output-directory $(TMP) $(REPORT).tex
	cp $(REPORT).bib $(TMP) && cd $(TMP) && bibtex $(REPORT).aux
	pdflatex -output-directory $(TMP) $(REPORT).tex
	pdflatex -output-directory $(TMP) $(REPORT).tex
	mv $(TMP)/$(REPORT).pdf .

clean:
	rm -r $(TMP)
