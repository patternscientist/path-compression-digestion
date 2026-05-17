# Path compression source-fidelity erratum

This erratum records the one remaining `PARTIAL` item from the source-anchor closure pass. It does not rewrite the accepted proof, alter theorem statements, or add new proof work.

## Erratum: shifting lemma wording in the source-fidelity block

The accepted proof note’s Section 2.3 states a shorthand shifting lemma with premise

```text
f(m,n,r) <= k m + n g(r)
```

while the recovered standalone `source_anchors.md` and the original source/paper Lemma 5 use the premise

```text
f(m,n,r) <= k m + 2n g(r)
```

and conclude

```text
f(m,n,r) <= (k+1)m + 2n g^diamond(r).
```

This is a source-fidelity wording mismatch in the source-fidelity block.

The accepted proof’s actual recurrence consequence

```text
f(m,n,r) <= k m + 2n J_k(r)
```

is source-anchored and remains unchanged.

No theorem statement or proof step in the accepted comparison theorem is altered by this erratum.
