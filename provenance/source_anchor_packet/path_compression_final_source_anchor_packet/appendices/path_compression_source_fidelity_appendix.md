# Source-fidelity appendix

This appendix is a packaging note for the accepted proof note

```text
accepted/path_compression_final_frontier_proof_note_ACCEPTED_FINAL.md
```

It does not modify the proof, restate the theorem statements, or add new proof work. Its purpose is only to identify where the accepted note’s packet definitions and recurrence dependencies are anchored in the provided archival materials.

## Source inventory

The archival bundle contains the accepted proof note and supporting/coordinator materials, but it does **not** contain a standalone `source_anchors.md` file. The coordinator brief lists `source_anchors.md` as a file in the patched worker packet, but that file is not present in this archival bundle.

Therefore this appendix distinguishes:

- **packet-internal anchor**: an explicit statement in the accepted proof note or supporting archival materials;
- **normalized packet convention**: a convention introduced to stabilize the comparison proof;
- **caveat**: a statement explicitly marked non-source-faithful under the current packet;
- **SOURCE-ANCHOR GAP**: a paper-level or standalone-`source_anchors.md` anchor not present in the provided archival materials.

## Anchor table

| # | Dependency | Available anchor in provided materials | How the accepted note uses it | Source-anchor status |
|---:|---|---|---|---|
| 1 | Definitions of \(g^*\) and \(g^\diamond\) | `accepted/path_compression_final_frontier_proof_note_ACCEPTED_FINAL.md`, §2.1, “The functions \(g^*\) and \(g^\diamond\)”: \(g^*(r)=\min\{t\ge0:g^{(t)}(r)\le1\}\), and \(g^\diamond(r)=g(r)\) if \(g(r)\le1\), otherwise \(1+g^\diamond(\lceil\log_2 g(r)\rceil)\). | Used directly as packet definitions. | Packet-internal anchor present. Paper-level/standalone `source_anchors.md` anchor absent from bundle: **SOURCE-ANCHOR GAP** if paper-level verification is required. |
| 2 | Definition of \(J_0\) and \(J_{k+1}=J_k^\diamond\) | Accepted note §2.2, “The \(J\) hierarchy”: \(J_0(r)=\lceil(r-1)/2\rceil\), \(J_{k+1}=J_k^\diamond\), with the displayed case expansion for \(J_{k+1}(r)\). | Used directly throughout the comparison proof. | Packet-internal anchor present. Paper-level/standalone anchor absent: **SOURCE-ANCHOR GAP** if required. |
| 3 | Top-down shifting lemma | Accepted note §2.3, “Shifting lemma and recurrence bound”: if \(f(m,n,r)\le km+ng(r)\), then \(f(m,n,r)\le(k+1)m+2n g^\diamond(r)\). | Used as a source dependency, not reproved. | Packet-internal anchor present as a recorded source-fidelity fact. Paper-level/standalone anchor absent: **SOURCE-ANCHOR GAP** if required. |
| 4 | Recurrence consequence \(f(m,n,r)\le km+2nJ_k(r)\) | Accepted note §2.3 states that iterating the shifting lemma with the \(J\) hierarchy gives \(f(m,n,r)\le km+2nJ_k(r)\). | Used directly in the final cost consequence. | Packet-internal anchor present. Paper-level/standalone anchor absent: **SOURCE-ANCHOR GAP** if required. |
| 5 | Source inverse threshold \(J_k(\lceil\log_2 n\rceil)\le 1+m/n\) | Accepted note §2.4, “Source inverse threshold”: “The current packet’s source anchor records the Seidel--Sharir inverse threshold as \(J_k(\lceil\log_2 n\rceil)\le 1+\frac mn\).” Supporting normalization note also states that the current packet’s `source_anchors.md` records \(1+m/n\), not \(2m/n\). | Used as the source-faithful threshold for \(\alpha_J^S\); converted from a real threshold to an integer-threshold statement with an additive \(+2\) shift, and \(+1\) when integral. | Packet-internal anchor present. The underlying standalone `source_anchors.md` is absent from this bundle: **SOURCE-ANCHOR GAP** if an independent anchor file or paper quote is required. |
| 6 | Packet rank cutoff \(L(n)=\lceil\log_2\max(n,2)\rceil\) | Accepted note §2.4 states the packet rank cutoff \(L(n)=\lceil\log_2\max(n,2)\rceil\) and explains agreement with \(\lceil\log_2 n\rceil\) for \(n\ge2\), with the \(n=1\) stabilization. | Used as a normalized packet convention. | Normalized packet convention present. Paper-level rank cutoff anchor absent from bundle: **SOURCE-ANCHOR GAP** if required. |
| 7 | Patched integer threshold \(Q(m,n)=\lceil1+m/n\rceil\) | Accepted note §2.5, “Patched integer threshold”: \(Q(m,n)=\lceil1+m/n\rceil\), introduced because the comparison theorem is stated for integer thresholds while \(1+m/n\) is real-valued. Coordinator brief §5 also lists \(Q(m,n)=\lceil1+m/n\rceil\) as a patched safe threshold. | Used as a normalized packet convention for the clean patched alpha comparison. | Normalized packet convention present. Not a paper/source threshold; it is a packet patch. |
| 8 | Caveat for alternate \(J_k(\lg n)\le2m/n\) threshold | Accepted note executive summary and §4.4 state that \(J_k(\lg n)\le2m/n\) is not source-faithful under the current packet unless independently verified, and is impossible for \(m/n<1/2\), \(n\ge3\). Supporting normalization note also warns that the current packet’s `source_anchors.md` records \(1+m/n\), not \(2m/n\). | Treated only as a caveat/alternate stricter target, not as a source-faithful threshold. | Caveat present. No paper-level anchor for \(2m/n\) is present; do not cite as source-faithful without independent verification. |

## Missing-anchor summary

The provided archival bundle does not include the standalone `source_anchors.md` referenced by the coordinator brief. Consequently, the appendix can package the accepted note’s source-fidelity dependencies and packet-internal anchors, but it cannot independently verify the original paper/source locations for the following items:

1. \(g^*\) and \(g^\diamond\);
2. \(J_0\) and \(J_{k+1}=J_k^\diamond\);
3. the top-down shifting lemma;
4. the recurrence consequence \(f(m,n,r)\le km+2nJ_k(r)\);
5. the source inverse threshold \(J_k(\lceil\log_2 n\rceil)\le1+m/n\);
6. the original rank cutoff convention before packet stabilization.

These are **SOURCE-ANCHOR GAP** items only in the archival-packaging sense: they are not proof errors in the accepted note. They mean that a future paper-ready archive should include either the original `source_anchors.md` file or explicit page/lemma/equation anchors from Seidel--Sharir and the packet source-fidelity pass.

## Safe packaging conclusion

For the accepted proof note, the dependencies needed by the proof are explicitly restated in the accepted note’s source-fidelity block. The normalized packet conventions \(L(n)=\lceil\log_2\max(n,2)\rceil\) and \(Q(m,n)=\lceil1+m/n\rceil\) are clearly identified as packet conventions, and the alternate \(2m/n\) threshold is clearly marked as non-source-faithful under the current packet unless independently verified.
