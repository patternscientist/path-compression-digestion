# Lean formalization lane

This directory is a bounded Lean 4 + mathlib lane for the threshold-comparison
core of the path-compression digestion paper. It is intentionally a scaffold,
not a formalization of the Seidel--Sharir recurrence.

## Release-layer context

The current paper/release layer is v0.2.1, a citation/bibliography-rendering
patch over v0.2.0. No theorem statements, proof constants, Lean formalization
content, or talk slides changed from v0.2.0.

For the current file-by-file theorem map and worker audit guide, see
`THEOREM_MAP.md`.

## What is formalized

### Abstract threshold comparison

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
* the threshold step from paper Lemma 4.3.

The threshold jump from paper Lemma 4.4 is now proved from those primitive
assumptions, rather than assumed as part of the core interface.

`PathCompressionDigestion/MainComparison.lean` proves row-domination and the
abstract comparison from `ThresholdCoreAssumptions R`:

```lean
theorem main_comparison_from_core :
  forall z Q, 1 <= z -> 1 <= Q -> A z (4*Q) <= R (z+1) Q
```

The older `MainComparisonAssumptions` wrapper remains as a compatibility layer,
but the current abstract main comparison is derived from the primitive
threshold assumptions.

### Concrete/infrastructure support

`PathCompressionDigestion/JBase.lean` formalizes the concrete base row
`J0 r = r / 2`, including the exact characterization corresponding to
`R_0(t) = 2*t + 1`.

`PathCompressionDigestion/CeilLog2.lean` wraps Mathlib's `Nat.clog 2` and proves
the termination estimates needed for a future formalization of the paper's
diamond recursion.

`PathCompressionDigestion/Diamond.lean` formalizes the paper's `g^diamond`
transform for natural-valued functions satisfying the required zero,
monotonicity, unboundedness, and strict-descent hypotheses. It proves the
equation lemmas and preservation facts for zero, pointwise bound, strict
descent, monotonicity, and unboundedness.

`PathCompressionDigestion/JHierarchy.lean` builds the recursive concrete
hierarchy:

```lean
J 0 r = J0 r
J (k+1) r = (JInput k).diamond r
```

It packages each row as a `DiamondInput` and proves the basic concrete `J_k`
facts: monotonicity, unboundedness, strict descent below the identity, pointwise
identity bound, successor-row bound, and level antitonicity.

`PathCompressionDigestion/ThresholdInverse.lean` provides generic finite
maximum/inverse infrastructure used by the concrete definition
`R_k(t) = max { r : J_k r <= t }`.

`PathCompressionDigestion/ThresholdInverseExtras.lean` adds generic support
lemmas for constructing threshold-inverse data from monotone, unbounded rows,
including eventual-growth lemmas, a constructor wrapper, a function-comparison
wrapper, and a successor escape lemma.

`PathCompressionDigestion/ConcreteThreshold.lean` defines the concrete
threshold inverse `R` for the `J` hierarchy and proves base exactness,
threshold monotonicity, level monotonicity, and concrete inverse/spec wrappers.

`PathCompressionDigestion/DiamondThreshold.lean` packages generic inverse data
for a `DiamondInput` row and its diamond transform, then proves the generic
diamond-to-threshold recurrence.

`PathCompressionDigestion/AlphaPrelude.lean` adds generic alpha/least-index
preparation and Ackermann buffer facts. This is preparation for later
paper-specific alpha/cost consequences, not the final paper alpha/cost theorem.

The Lean root file `PathCompressionDigestion.lean` imports these concrete
support modules along with the Ackermann, threshold, and main-comparison
modules.

## What is intentionally not formalized

This lane does not formalize:

* the source Seidel--Sharir path-compression recurrence;
* the proof that the concrete `R` satisfies `ThresholdCoreAssumptions`;
* the concrete main-comparison corollary obtained by instantiating
  `main_comparison_from_core`;
* paper-specific alpha definitions, cost consequences, source anchors, or
  release packaging.

Those are out of scope for this first pass.

## Proof status

The Ackermann package in `PathCompressionDigestion/Ackermann.lean` is now
proof-complete for the four public facts mapped to paper Lemma 4.5 and its
exponential corollary.

The row-domination invariant and main comparison are now proved from
`ThresholdCoreAssumptions R` alone. The concrete maximum definition of
`R_k(t)` is formalized, but the project is still intentionally abstract at the
core threshold-engine boundary: the proof that this concrete `R` satisfies
`ThresholdCoreAssumptions` is not yet formalized.

The concrete base row, `ceilLog2` support facts, diamond transform, recursive
concrete `J_k` hierarchy, generic threshold-inverse infrastructure, generic
threshold-inverse extras, concrete threshold inverse `R`, generic
diamond-to-threshold recurrence, and generic alpha prelude are present as setup
for future concrete core and paper-specific alpha/cost work.

## Build

From this directory:

```powershell
lake build PathCompressionDigestion
lake env lean PathCompressionDigestion.lean
```

The project was created with the mathlib Lake template and is pinned by
`lean-toolchain`.

For docs-only branches, use `git diff --check` and the source-only
`sorry`/`admit`/`axiom` scan. For Lean source branches, use targeted module
checks and do not force a full Mathlib rebuild for every branch.

## Paper map

| Lean file/theorem | Paper location |
|---|---|
| `Ackermann.A` | Section 4.1, Ackermann normalization |
| `Ackermann.monotone_right` | Lemma 4.5(1) |
| `Ackermann.ge_two_mul` | Lemma 4.5(2) |
| `Ackermann.row_domination` | Lemma 4.5(3) |
| `Ackermann.one_eq_pow` | Corollary after Lemma 4.5 |
| `DiamondInput.diamond` and preservation facts | Diamond preservation lemma / diamond transform setup |
| `J`, `J_zero_row`, `J_succ_row`, `J_monotone`, `J_unbounded`, `J_succ_le`, `J_level_antitone` | Basic `J_k` package |
| `ThresholdInverse.thresholdInverse` and generic max facts | Generic setup for `R_k(t)` |
| `ThresholdInverse.Data.of_monotone_unbounded` and extras | Generic setup for concrete threshold inverse construction |
| `R`, `R_zero_eq`, `R_monotone_threshold`, `R_monotone_level`, `J_R_le`, `le_R_of_J_le`, `lt_J_of_R_lt` | Concrete threshold inverse package |
| `DiamondInput.threshold_step` | Generic diamond-to-threshold recurrence |
| `Abstract.alphaOf` and alpha prelude facts | Generic preparation for later alpha consequences |
| `Abstract.ThresholdCoreAssumptions.baseExact` | Section 4.4, exact base inverse |
| `Abstract.ThresholdCoreAssumptions.thresholdStep` | Lemma 4.3 |
| `Abstract.threshold_jump_from_step` | Lemma 4.4 |
| `Abstract.row_domination_invariant` | Lemma 4.6 |
| `Abstract.small_Q_one` | Theorem 4.7, `Q=1` cases |
| `Abstract.main_comparison_from_core` | Theorem 4.7 main comparison |
| `Abstract.MainComparisonAssumptions` / `Abstract.main_comparison` | Legacy wrapper for the original scaffold interface |
