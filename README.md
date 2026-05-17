# Path Compression Proof Digestion

Publication-facing mathematical artifact for the path-compression proof-digestion project.

## Current purpose

This repository packages a source-anchored proof note showing that the Seidel--Sharir top-down `J` hierarchy implies the packet-normalized inverse-Ackermann bound.

## Main theorem

```text
R_k(t)=max{r>=0:J_k(r)<=t}
R_{z+1}(Q) >= A(z,4Q)
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
```

## Start here

- Proof note: `proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md`
- Audit: `audits/path_compression_v2_integrated_proof_note_AUDIT.md`
- Finite sanity check: `scripts/sanity_check_j_thresholds.py`
- Source anchors: `provenance/source_anchor_packet/path_compression_final_source_anchor_packet/source_anchors/source_anchors.md`

## Folder map

```text
proof_note/
  Current integrated proof note.

publication/
  Human-facing abstract and talk outline.

audits/
  Self-audit, verification report, changelog, and audit notes.

manifests/
  Worker-produced publication packet manifest.

provenance/
  Source-anchor packet and original uploaded zips used to build this clean folder.

scripts/
  Mechanical sanity checks and release helpers.

prompts/
  Copy-paste Codex prompts for bounded tasks.

release/
  Place rebuilt release zips here.
```

## Important status note

The latest worker zip contained five files:

- `path_compression_v2_2_integrated_proof_note_public_packaging.md`
- `path_compression_v2_2_publication_packet_manifest.md`
- `path_compression_v2_2_publication_packaging_VERIFICATION.md`
- `path_compression_v2_2_changelog.md`
- `path_compression_v2_2_self_audit.md`

The v2.2 manifest also references `path_compression_v2_integrated_proof_note_AUDIT.md`. That audit file was recovered after the first clean-folder build and is now included in `audits/`. See `audits/README.md`.

## Development / reproducibility

Open this folder as its own Codex project for bounded mechanical audit, packaging, and reproducibility work.

Suggested first Git commands:

```powershell
git init
git add .
git commit -m "Initialize clean path compression digestion workspace"
```
