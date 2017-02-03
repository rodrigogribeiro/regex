default: pdf

pdf:
	lhs2TeX --agda regex.lagda > regex.tex
	pdflatex regex
	pdflatex regex
	bibtex regex
	pdflatex regex
