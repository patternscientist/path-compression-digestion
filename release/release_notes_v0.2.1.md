# v0.2.1: Fix paper bibliography citation rendering

Patch release for v0.2.0.

This release fixes the compiled paper PDF so the introduction and bibliography render citations correctly instead of showing unresolved `[?]` markers.

Changes:
- corrected the paper bibliography database wiring;
- added BibTeX entries for Seidel--Sharir 2005, Tarjan 1975, and Dagstuhl 25191;
- rebuilt `paper/main.pdf` with resolved citations.

No theorem statements, proof constants, Lean formalization content, or talk slides changed from v0.2.0.
