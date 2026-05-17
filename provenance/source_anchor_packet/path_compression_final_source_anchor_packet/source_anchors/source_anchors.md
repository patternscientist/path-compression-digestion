# Source Anchors and Fidelity Checklist

Date: 2026-05-17

This file exists to prevent the worker chat from proving a nearby but source-mismatched theorem. The first worker response should do a compact source-fidelity check against this file before beginning the proof attack. This check does **not** count as one of the five proof-work hits.

## Public problem anchor

The public target is Section 5.3, "Top-down analysis of path compression," in the Dagstuhl report *Adaptive and Scalable Data Structures*.

The report states that Seidel and Sharir gave an inverse-Ackermann upper bound for path compression using a top-down recurrence; the analysis uses a related function called `J`, not Ackermann explicitly; and the problem is to give a simple, direct proof of the inverse-Ackermann bound using their top-down recurrence and the classical Ackermann definition.

Primary URL:

```text
https://drops.dagstuhl.de/storage/04dagstuhl-reports/volume15/issue05/25191/html/DagRep.15.5.1/DagRep.15.5.1.html
```

Verbatim prompt quote, from Dagstuhl Report 15(5), Seminar 25191, Section 5.3 "Top-down analysis of path compression":

> “Seidel and Sharir gave a proof of the inverse-Ackermann-function upper bound for path compression based on a beautiful top-down recurrence. The analysis does not use Ackermann’s function explicitly, but uses a related function they call ‘J.’ Problem: Give a simple, direct proof of the inverse-Ackermann function bound using their top-down recurrence and the classical definition of Ackermann’s function.”

## Technical source anchor

Seidel--Sharir source:

```text
Raimund Seidel and Micha Sharir,
Top-Down Analysis of Path Compression,
SIAM Journal on Computing 34(3):515--525, 2005.
DOI: 10.1137/S0097539703439088
Author PDF: https://www.math.tau.ac.il/~michas/ufind.pdf
```

The article abstract says the analysis is top-down, gives recurrence relations from which the bounds arise naturally, and derives the inverse-Ackermann-style bound without introducing Ackermann explicitly.

## Exact source checkpoints

Before doing the proof attack, verify these against the source or against `recurrence_statement.md` if browsing is disabled:

### Checkpoint A: rank forest and maximum rank

Source page 7 states that a node of rank `k` roots a subtree of size at least `2^k`, hence the maximum rank is at most `log_2 n` for a forest with `n` nodes.

Packet convention:

```text
L(n) = ceil(log_2 max(n,2))
```

This is intentionally slightly padded so all floor/ceiling choices are harmless.

### Checkpoint B: `g^*` and `g^diamond`

Source page 7 defines, for integer `g` with `g(r) < r` for positive `r`,

```text
g*(r) = 0                         if r <= 1
      = 1 + g*(g(r))              if r > 1

g^diamond(r) = g(r)                                if g(r) <= 1
             = 1 + g^diamond(ceil(log_2 g(r)))     if g(r) > 1.
```

The source notes that `g^diamond` is essentially `(log o g)^*`.

### Checkpoint C: shifting lemma

Source pages 7--8 state the shifting lemma:

```text
If f(m,n,r) <= k m + 2 n g(r)
for a nondecreasing integer function g with g(r) < r for r > 0,
then
f(m,n,r) <= (k+1)m + 2 n g^diamond(r).
```

### Checkpoint D: `J_k` hierarchy and cost bound

Source page 9 states Corollary 6:

```text
J_0(r) = ceil((r - 1)/2),
J_k(r) = J_{k-1}^diamond(r) for k > 0,
```

and then

```text
f(m,n,r) <= k m + 2 n J_k(r).
```

### Checkpoint E: source inverse threshold

Source page 9 defines

```text
alpha_S(m,n) = min { k in N : J_k(ceil(log_2 n)) <= 1 + m/n }.
```

It then obtains

```text
f(m,n,r) <= (alpha_S(m,n) + 2)m + 2n
```

and hence the union-find time bound.

### Checkpoint F: relation to classical inverse Ackermann

Source page 10 says the reader may wonder how `alpha_S` relates to Tarjan's initial inverse-Ackermann function `alpha_T`; it defines `alpha_T` via a different hierarchy `T_k` and states that the differences between `alpha_S` and `alpha_T` are minor and asymptotically equivalent.

This project attacks the stronger digestion target of giving a direct comparison from the `J_k` hierarchy to a classical Ackermann normalization.

## Source-fidelity pass required from worker

Before Hit 1, the worker must output:

1. whether `recurrence_statement.md` matches Checkpoints A--F;
2. any harmless changes of notation;
3. any real mismatch requiring target repair;
4. the exact definitions it will use for `L(n)`, `Q(m,n)`, `S_Q(m,n)`, `A`, and `alpha_Q(m,n)`.

This source-fidelity pass does **not** count as a proof-work hit.
