MAIN=patterns-paper
PROG=InconsistentConstraints

all:
	pdflatex $(MAIN)

bib:
	pdflatex $(MAIN)
	bibtex $(MAIN)
	pdflatex $(MAIN)
	bibtex $(MAIN)
	pdflatex $(MAIN)

prog:
	ocamlopt -o $(PROG) $(PROG).ml

clean: 
	rm -f *.aux *.log *.out $(MAIN).bbl main.blg main.pdf

