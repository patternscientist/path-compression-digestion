# Formalization Status

This document records the current boundary between the paper/proof-note packet
and the Lean formalization lane. It is a status note, not a theorem statement
and not a claim of full formalization of the Seidel--Sharir recurrence.

## Paper/proof-note layer

The publication-facing mathematical packet is the v2.2 proof note:

- `proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md`

The current release-layer status is v0.2.1. This is a
citation/bibliography-rendering patch over v0.2.0: it fixes unresolved
compiled-paper citation markers, but does not change theorem statements, proof
constants, Lean formalization content, or talk slides from v0.2.0.

For the current file-by-file Lean theorem map and worker audit guide, see:

- `formalization/lean/THEOREM_MAP.md`

At the paper/proof-note layer, the target comparison remains

```text
R_{z+1}(Q) >= A(z,4Q)
```

with

```text
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
```

## Current abstract Lean layer

The abstract Lean layer formalizes the packet Ackermann package and an
abstract threshold engine. Its boundary is:

```lean
ThresholdCoreAssumptions R
```

The comparison results are proved for any abstract threshold family `R`
satisfying those assumptions. The threshold jump is derived from the primitive
assumptions, and the row-domination/main comparison lane is now proved from
`ThresholdCoreAssumptions R`.

In particular, the abstract theorem currently built by Lean is the conditional
comparison

```lean
forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q
```

under `ThresholdCoreAssumptions R`.

## Current concrete/infrastructure Lean layer

- `formalization/lean/PathCompressionDigestion/JBase.lean` formalizes the
  concrete base row `J0 r = r / 2`.
- `JBase.lean` proves the base inverse facts, including the exact
  characterization corresponding to `R_0(t) = 2*t + 1`.
- `formalization/lean/PathCompressionDigestion/CeilLog2.lean` wraps
  `Nat.clog 2` and proves termination estimates used by the diamond recursion.
- `formalization/lean/PathCompressionDigestion/Diamond.lean` formalizes the
  concrete `g^diamond` transform and its preservation package.
- `formalization/lean/PathCompressionDigestion/JHierarchy.lean` formalizes the
  recursive concrete `J_k` hierarchy using the diamond transform.
- `formalization/lean/PathCompressionDigestion/ThresholdInverse.lean` provides
  generic finite maximum/inverse infrastructure used by the concrete
  definition `R_k(t) = max { r : J_k r <= t }`.
- `formalization/lean/PathCompressionDigestion/ThresholdInverseExtras.lean`
  provides generic support lemmas for constructing threshold-inverse data from
  monotone, unbounded rows, supporting the concrete `R` and diamond-threshold
  work.
- `formalization/lean/PathCompressionDigestion/ConcreteThreshold.lean`
  defines the concrete threshold inverse `R` for the `J` hierarchy and proves
  base exactness, threshold monotonicity, level monotonicity, and concrete
  inverse/spec wrappers.
- `formalization/lean/PathCompressionDigestion/DiamondThreshold.lean` proves
  the generic diamond-to-threshold recurrence for a `DiamondInput` row and its
  diamond transform.
- `formalization/lean/PathCompressionDigestion/AlphaPrelude.lean` provides
  generic alpha/least-index preparation and Ackermann buffer facts. It is not
  the final paper-specific alpha/cost formalization.
- `formalization/lean/PathCompressionDigestion.lean` imports these concrete
  support modules along with the abstract comparison modules.

## Proved in Lean

- The packet Ackermann package in
  `formalization/lean/PathCompressionDigestion/Ackermann.lean`.
- Threshold jump from `ThresholdCoreAssumptions` in
  `formalization/lean/PathCompressionDigestion/Threshold.lean`.
- Row-domination and main comparison from `ThresholdCoreAssumptions` in
  `formalization/lean/PathCompressionDigestion/MainComparison.lean`.
- The diamond transform and preservation facts in
  `formalization/lean/PathCompressionDigestion/Diamond.lean`.
- The recursive concrete `J_k` hierarchy and basic package in
  `formalization/lean/PathCompressionDigestion/JHierarchy.lean`.
- Generic threshold-inverse extras in
  `formalization/lean/PathCompressionDigestion/ThresholdInverseExtras.lean`.
- The concrete threshold inverse `R` and its base, monotonicity, and inverse
  wrappers in
  `formalization/lean/PathCompressionDigestion/ConcreteThreshold.lean`.
- The generic diamond-to-threshold recurrence in
  `formalization/lean/PathCompressionDigestion/DiamondThreshold.lean`.
- Generic alpha prelude facts in
  `formalization/lean/PathCompressionDigestion/AlphaPrelude.lean`.
- The concrete base-row facts and generic infrastructure listed above.

## Not Yet Proved in Lean

- The proof that the concrete `R` satisfies `ThresholdCoreAssumptions`.
- The concrete main-comparison corollary obtained by applying
  `main_comparison_from_core` to a concrete `R`.
- The direct paper consequence `A z (4*Q) > r -> J (z+1) r <= Q`.
- The paper-specific alpha definitions and cost consequences.
- The source Seidel--Sharir recurrence itself.

## Build Check

From `formalization/lean/`:

```powershell
lake build PathCompressionDigestion
lake env lean PathCompressionDigestion.lean
```

The GitHub Actions workflow `.github/workflows/lean-formalization.yml` runs
this build lane using the toolchain pinned by
`formalization/lean/lean-toolchain`.

For docs-only branches, use `git diff --check` and the source-only
`sorry`/`admit`/`axiom` scan. For Lean source branches, use targeted module
checks and avoid forcing a full Mathlib rebuild for every branch.
