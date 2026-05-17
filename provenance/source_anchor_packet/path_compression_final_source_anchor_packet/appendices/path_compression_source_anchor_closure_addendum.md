# Source-anchor closure addendum

This addendum follows the accepted source-fidelity appendix and treats the accepted proof note as read-only:

```text
accepted/path_compression_final_frontier_proof_note_ACCEPTED_FINAL.md
```

It does not rewrite the proof, alter theorem statements, or add new proof work. Its only purpose is to close or reduce the previously identified `SOURCE-ANCHOR GAP` items.

## Recovered anchor inventory

A standalone `source_anchors.md` file was recovered from the original worker packet:

```text
path_compression_frontier_attack_packet_patched_2026_05_17_v4.zip
└── path_compression_frontier_attack_packet_patched_2026_05_17/source_anchors.md
```

The accepted archival bundle itself does not contain a standalone `source_anchors.md` file.

```text
source_anchors.md in accepted archival bundle: no
source_anchors.md in recovered worker packet: yes
```

The recovered `source_anchors.md` identifies the technical source as:

```text
Raimund Seidel and Micha Sharir,
Top-Down Analysis of Path Compression,
SIAM Journal on Computing 34(3):515--525, 2005.
DOI: 10.1137/S0097539703439088
Author PDF: https://www.math.tau.ac.il/~michas/ufind.pdf
```

A compact direct source check against the author PDF confirms the same page-level anchors used by `source_anchors.md`:

- page 7: maximum rank at most \(\log_2 n\), definitions of \(g^*\) and \(g^\diamond\), and the statement of the shifting lemma;
- page 8: proof/conclusion of the shifting lemma;
- page 9: Corollary 6 defining \(J_0\), \(J_k=J_{k-1}^\diamond\), the recurrence \(f(m,n,r)\le km+2nJ_k(r)\), and \(\alpha_S(m,n)=\min\{k\in\mathbb N:J_k(\lceil\log_2 n\rceil)\le 1+m/n\}\);
- page 10: comparison discussion with Tarjan’s different \(T_k\)-based inverse, not a replacement \(J_k\)-threshold \(2m/n\).

## Closure table

| dependency | current packet anchor | recovered source anchor | status |
|---|---|---|---|
| \(g^*\) and \(g^\diamond\) | Accepted note §2.1 restates \(g^*(r)=\min\{t\ge0:g^{(t)}(r)\le1\}\) and the recursive \(g^\diamond\) definition. `recurrence_statement.md` §2 restates the same definitions. | Recovered `source_anchors.md`, Checkpoint B: source page 7 defines \(g^*\) and \(g^\diamond\) for integer \(g\) with \(g(r)<r\) for \(r>0\), and notes \(g^\diamond\) is essentially \((\log\circ g)^*\). Direct PDF check: page 7 displays these definitions. | CLOSED |
| \(J_0\) and \(J_{k+1}=J_k^\diamond\) | Accepted note §2.2 and `recurrence_statement.md` §3 define \(J_0(r)=\lceil(r-1)/2\rceil\) and \(J_{k+1}=J_k^\diamond\). | Recovered `source_anchors.md`, Checkpoint D: source page 9 states Corollary 6 with \(J_0(r)=\lceil(r-1)/2\rceil\) and \(J_k(r)=J_{k-1}^\diamond(r)\) for \(k>0\). Direct PDF check: page 9 displays Corollary 6. | CLOSED |
| top-down shifting lemma | Accepted note §2.3 states a shifting lemma in shorthand form with premise \(f(m,n,r)\le km+ng(r)\). `recurrence_statement.md` §2 states the source-compatible form with premise \(f(m,n,r)\le km+2ng(r)\). | Recovered `source_anchors.md`, Checkpoint C: source pages 7--8 state Lemma 5 with premise \(f(m,n,r)\le km+2ng(r)\) and conclusion \(f(m,n,r)\le(k+1)m+2ng^\diamond(r)\). Direct PDF check: page 7 states the lemma, page 8 completes the proof. This closes the source lemma with the \(2n\) coefficient, but not the accepted note’s shorthand \(n g(r)\) premise. | PARTIAL |
| recurrence \(f(m,n,r)\le km+2nJ_k(r)\) | Accepted note §2.3 and `recurrence_statement.md` §3 state the iterated recurrence consequence. | Recovered `source_anchors.md`, Checkpoint D: source page 9 states Corollary 6 and then \(f(m,n,r)\le km+2nJ_k(r)\). Direct PDF check: page 9 displays the recurrence. | CLOSED |
| source inverse threshold \(J_k(\lceil\log_2 n\rceil)\le1+m/n\) | Accepted note §2.4 and §4.2 define the source-faithful threshold through \(1+m/n\). | Recovered `source_anchors.md`, Checkpoint E: source page 9 defines \(\alpha_S(m,n)=\min\{k\in\mathbb N:J_k(\lceil\log_2 n\rceil)\le1+m/n\}\). Direct PDF check: page 9 displays this formula. | CLOSED |
| original rank cutoff convention before packet stabilization | Accepted note §2.4 uses \(L(n)=\lceil\log_2\max(n,2)\rceil\), explaining agreement with \(\lceil\log_2 n\rceil\) for \(n\ge2\). `normalization_conventions.md` §2 records the reason for the padded cutoff. | Recovered `source_anchors.md`, Checkpoint A: source page 7 says a node of rank \(k\) roots a subtree of size at least \(2^k\), hence maximum rank is at most \(\log_2 n\). Direct PDF check: page 7 states this bound. | CLOSED |
| packet rank cutoff \(L(n)=\lceil\log_2\max(n,2)\rceil\) | Accepted note §2.4, `recurrence_statement.md` §1, and `normalization_conventions.md` §2 define the padded \(L(n)\). | Recovered `source_anchors.md`, Checkpoint A records \(L(n)=\lceil\log_2\max(n,2)\rceil\) as the packet convention, intentionally padded so floor/ceiling choices are harmless. This is a packet normalization anchored to the original \(\log_2 n\) rank bound. | CLOSED |
| patched integer threshold \(Q(m,n)=\lceil1+m/n\rceil\) | Accepted note §2.5, `recurrence_statement.md` §4, and `normalization_conventions.md` §3 define \(Q(m,n)=\lceil1+m/n\rceil\). | Recovered `source_anchors.md`, Checkpoint E closes the source threshold \(1+m/n\). `normalization_conventions.md` §3 supplies the packet patch \(Q=\lceil1+m/n\rceil\), explaining that \(Q\) is integer-valued and \(Q\le2+m/n\). This is a packet normalization, not an original paper threshold. | CLOSED |
| caveat for alternate \(J_k(\lg n)\le2m/n\) | Accepted note executive summary and §4.4 treat \(2m/n\) as non-source-faithful under the current packet unless independently verified. | Recovered `source_anchors.md`, Checkpoint E anchors the \(J_k\)-source threshold as \(1+m/n\), not \(2m/n\). Direct PDF check: page 9 displays \(1+m/n\) in \(\alpha_S\). Direct PDF check: page 10 discusses Tarjan’s separate \(T_k\)-based \(\alpha_T\) threshold involving \(m/n\), not a \(J_k\)-threshold \(2m/n\). No recovered source anchor supports \(J_k(\lg n)\le2m/n\) as source-faithful. | CLOSED |

## Remaining note on the PARTIAL item

The only non-closed item is the **shifting lemma as worded in the accepted proof note’s source-fidelity block**. The recovered standalone source anchor and direct paper check support the source lemma with premise

\[
f(m,n,r)\le km+2n g(r),
\]

not the accepted note’s shorthand premise

\[
f(m,n,r)\le km+n g(r).
\]

This is classified as `PARTIAL` rather than `STILL GAP` because:

1. the source lemma itself is recovered and explicitly anchored;
2. the accepted proof’s later cost argument uses the recurrence consequence \(f(m,n,r)\le km+2nJ_k(r)\), which is separately `CLOSED`;
3. no theorem statement in the accepted note is changed by this packaging addendum.

## Closure summary

| status | count |
|---|---:|
| CLOSED | 8 |
| PARTIAL | 1 |
| STILL GAP | 0 |

The previously identified source-anchor gaps are therefore reduced to one coefficient-wording mismatch in the source-fidelity restatement of the shifting lemma. The recurrence actually used by the accepted proof is source-anchored.
