# Final Source-Anchor Packet Manifest

This coordinator-generated manifest records the contents of `path_compression_final_source_anchor_packet`.

## Packet status

- Accepted proof note: included and read-only.
- Recovered standalone `source_anchors.md`: included.
- Source-fidelity appendix: included.
- Source-anchor closure addendum and audit: included.
- Source-fidelity erratum: included.
- Worker final source-anchor manifest: included.

## Important caveat

The source-fidelity erratum records the one remaining partial item: the accepted proof note's source-fidelity block states a shorthand shifting lemma premise with `n g(r)`, while the recovered source/paper lemma uses `2n g(r)`. The recurrence actually used by the proof, `f(m,n,r) <= k m + 2n J_k(r)`, is source-anchored and unchanged.

## SHA-256 hashes

See `SHA256SUMS` for exact hashes of all included files.
