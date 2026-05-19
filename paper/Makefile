LATEXMK ?= latexmk
PAPER_TEX ?= main.tex

.PHONY: all clean

all:
	$(LATEXMK) -pdf $(PAPER_TEX)

clean:
	$(LATEXMK) -C $(PAPER_TEX)
