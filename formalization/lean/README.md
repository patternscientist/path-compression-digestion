# Lean formalization scaffold

This directory is a bounded Lean 4 + mathlib lane for the threshold-comparison
core of the path-compression digestion paper. It is intentionally a scaffold,
not a formalization of the Seidel--Sharir recurrence.

## What is formalized

The project defines the packet Ackermann function on `Nat` in
`PathCompressionDigestion/Ackermann.lean`:

```lean
A 0 x = 2 * x
A (i+1) 0 = 0
A (i+1) 1 = 2
A (i+1) (x+2) = A i (A (i+1) (x+1))
```

It also defines an abstract threshold family `R : Nat -> Nat -> Nat` in
`PathCompressionDigestion/Threshold.lean` and records the assumptions used by
the paper's threshold engine:

* `R 0 t = 2*t + 1`;
* monotonicity in the threshold parameter;
* monotonicity in the level;
* the threshold step from paper Lemma 4.3;
* the threshold jump from paper Lemma 4.4.

`PathCompressionDigestion/MainComparison.lean` proves the abstract comparison

```lean
theorem main_comparison :
  forall z Q, 1 <= z -> 1 <= Q -> A z (4*Q) <= R (z+1) Q
```

from the threshold assumptions, the row-domination invariant corresponding to
paper Lemma 4.6, and the paper's explicit `Q = 1` case split in Theorem 4.7.

## What is intentionally not formalized

This lane does not formalize:

* the source Seidel--Sharir path-compression recurrence;
* the source paper's `g^diamond` termination argument;
* the concrete `J_k` hierarchy;
* the concrete maximum definition of `R_k(t) = max { r >= 0 : J_k(r) <= t }`;
* alpha definitions, cost consequences, source anchors, or release packaging.

Those are out of scope for this first pass.

## Remaining `sorry`s

There are four `sorry`s, all in `PathCompressionDigestion/Ackermann.lean`:

* `Ackermann.monotone_right`, paper Lemma 4.5(1);
* `Ackermann.ge_two_mul`, paper Lemma 4.5(2);
* `Ackermann.row_domination`, paper Lemma 4.5(3);
* `Ackermann.one_eq_pow`, the corollary `A(1,y)=2^y` for `y>=1`.

The threshold and comparison layer has no `sorry`; it is abstracted by explicit
structure hypotheses corresponding to paper Lemmas 4.2--4.7.

## Build

From this directory:

```powershell
lake exe cache get
lake build
```

The project was created with the mathlib Lake template and is pinned by
`lean-toolchain`.

## Paper map

| Lean file/theorem | Paper location |
|---|---|
| `Ackermann.A` | Section 4.1, Ackermann normalization |
| `Ackermann.monotone_right` | Lemma 4.5(1) |
| `Ackermann.ge_two_mul` | Lemma 4.5(2) |
| `Ackermann.row_domination` | Lemma 4.5(3) |
| `Ackermann.one_eq_pow` | Corollary after Lemma 4.5 |
| `Abstract.ThresholdAssumptions.baseExact` | Section 4.4, exact base inverse |
| `Abstract.ThresholdAssumptions.thresholdStep` | Lemma 4.3 |
| `Abstract.ThresholdAssumptions.thresholdJump` | Lemma 4.4 |
| `Abstract.MainComparisonAssumptions.rowDominationInvariant` | Lemma 4.6 |
| `Abstract.MainComparisonAssumptions.smallQOne` | Theorem 4.7, `Q=1` cases |
| `Abstract.main_comparison` | Theorem 4.7 main comparison |
