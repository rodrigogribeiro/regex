default: pdf

pdf:
	lhs2TeX --agda paper.lagda > paper.tex
	pdflatex paper
	pdflatex paper
	bibtex paper
	pdflatex paper
