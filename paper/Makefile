LATEXMK ?= latexmk
TEX ?= main.tex

.PHONY: all clean

all:
	$(LATEXMK) -pdf $(TEX)

clean:
	$(LATEXMK) -C $(TEX)
