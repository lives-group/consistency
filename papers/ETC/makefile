default: pdf

pdf:
	coqdoc --latex --no-preamble --parse-comments -s -o consistency.tex consistency.v
	pdflatex template.tex
	pdflatex template.tex
	bibtex template
	pdflatex template.tex
