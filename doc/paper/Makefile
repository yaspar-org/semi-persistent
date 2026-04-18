all: egraphs2026.pdf

egraphs2026.pdf: egraphs2026.tex
	pdflatex -interaction=nonstopmode egraphs2026.tex
	pdflatex -interaction=nonstopmode egraphs2026.tex

clean:
	rm -f *.aux *.log *.out *.bbl *.blg *.pdf

.PHONY: all clean
