# AGENTS.md

This repository contains a publication-facing proof-digestion packet for the path-compression project.

## Core instruction

Do not perform open-ended proof discovery unless explicitly asked.

The current goal is to polish, audit, mechanically validate, and package a source-anchored proof note showing that the Seidel--Sharir top-down `J` hierarchy implies an inverse-Ackermann bound under the packet normalization.

## Allowed work

- Fix manifest/file-list inconsistencies.
- Patch stale filenames and stale version references.
- Add or improve mechanical sanity-check scripts.
- Generate dependency DAGs.
- Create release/build scripts.
- Make minimal wording patches for logical precision.
- Produce audit reports.
- Preserve source fidelity.

## Forbidden work without explicit permission

- Do not rewrite the proof architecture.
- Do not change theorem statements.
- Do not broaden into a literature review.
- Do not replace the proof with a Tarjan-style bottom-up potential proof.
- Do not claim a new union-find bound.
- Do not silently change normalizations.

## Required mathematical invariants

The current packet target is:

```text
R_{z+1}(Q) >= A(z,4Q)
```

with:

```text
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
```

The core constants are:

```text
c = 1, C = 1, D = 4
```

Any change touching these definitions must be flagged as high risk.

## Expected workflow

1. Read `README.md`, this file, and `CURRENT_STATUS.md`.
2. Treat `proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md` as the current proof note.
3. Treat `provenance/source_anchor_packet/` as source/provenance material.
4. Use `scripts/sanity_check_j_thresholds.py` only as a finite off-by-one sanity check. It is not a proof.
5. Use Git diffs. Make minimal changes and report every changed file.
