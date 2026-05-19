# GitHub update drop-in v1

This drop-in is intended to be extracted at the **repository root** of
`path-compression-digestion` after merging `origin/lean-threshold-jump-derived-v1`
into a fresh integration branch from `main`.

It contains the final red-team-repaired paper and talk artifacts:

- `paper/main.tex`
- `paper/main.pdf`
- `paper/refs.bib`
- `audits/integer_threshold_patch_report.md`
- `audits/redteam_minor_repairs_report.md`
- `publication/slides/inverting_path_compression_beamer_v7.tex`
- `publication/slides/inverting_path_compression_beamer_v7.pdf`
- `release/path_compression_j_to_ackermann_redteam_minor_repairs_bundle.zip`

This v1 drop-in explicitly uses:

- `path_compression_j_to_ackermann_redteam_minor_repairs.tex` as `paper/main.tex`;
- `path_compression_j_to_ackermann_redteam_minor_repairs.pdf` as `paper/main.pdf`.

If `github_update_dropin_v0.zip` was already extracted but not committed, extracting
this v1 zip at the repo root is safe: it overwrites the same target files with the
final versions.

Suggested validation:

```powershell
git status
git diff --stat
git diff -- paper/main.tex

cd paper
make clean
make
cd ..

python scripts/sanity_check_j_thresholds.py

cd formalization/lean
lake build
cd ../..
```

Then stage and commit the intended paths only.
