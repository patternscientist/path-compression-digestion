# Paper Exposition Package

This folder contains a human-facing LaTeX exposition of the packet proof.
It is additive packaging only: it does not replace or edit the Markdown
proof note.

## Build

Preferred command:

```sh
make
```

This runs:

```sh
latexmk -pdf main.tex
```

Fallback if `latexmk` is unavailable:

```sh
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

Clean generated files:

```sh
make clean
```

## Files

- `main.tex`: exposition paper using `amsart`.
- `macros.tex`: package imports, theorem environments, and local macros.
- `refs.bib`: source-anchor bibliography entries.
- `Makefile`: build and clean targets.

The finite script `../scripts/sanity_check_j_thresholds.py` is only an
off-by-one sanity check; it is not part of the mathematical proof.
