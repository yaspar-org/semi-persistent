all: slides.pdf

slides.pdf: slides.tex
	pdflatex -interaction=nonstopmode slides.tex
	pdflatex -interaction=nonstopmode slides.tex

clean:
	rm -f *.aux *.log *.out *.nav *.snm *.toc *.vrb *.pdf

.PHONY: all clean
