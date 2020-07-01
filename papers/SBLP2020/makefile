default: pdf

pdf:
	coqdoc --latex --no-preamble --parse-comments -s -o consistency.tex consistency.v
	pdflatex paper.tex
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
