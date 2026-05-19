# v0.2.0: Final red-team-audited paper, Lean integration, and talk deck

This release publishes the merged proof-digestion artifact set for the Seidel--Sharir `J` hierarchy to classical Ackermann comparison.

Highlights:
- final paper-style LaTeX/PDF with the integer-threshold fix for `R_k(t)`;
- minor red-team repairs to the Ackermann-domination exposition and conclusion framing;
- Lean formalization integration through the abstract threshold/Ackermann engine;
- Beamer talk deck for the Lean/AI club proof-digestion presentation;
- audit reports, source-anchor materials, and release bundle.

Main mathematical comparison:
`R_{z+1}(Q) >= A(z, 4Q)` for `z >= 1`, `Q >= 1`.

Scope:
This is a source-faithful proof-digestion/exposition release responding to Tarjan's Dagstuhl 25191 Section 5.3 comparison prompt. It does not claim a new union-find upper bound or a sweeping priority claim.

Recommended start points:
- `paper/main.pdf`
- `publication/slides/inverting_path_compression_beamer_v7.pdf`
- `formalization/FORMALIZATION_STATUS.md`
- `audits/redteam_minor_repairs_report.md`
