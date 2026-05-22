# Lean formalization lane

This directory is a bounded Lean 4 + mathlib lane for the threshold-comparison
core, concrete `J`/threshold infrastructure, paper-specific alpha comparison,
conditional source-cost consequence, and source-shifting iteration bridge of
the path-compression digestion paper. It is not yet a formalization of the
Seidel--Sharir path-compression model.

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
the termination estimates used by the paper's diamond recursion.

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

`PathCompressionDigestion/ConcreteCore.lean` connects the concrete `R` family
to the generic diamond-threshold inverses for `JInput`:

```lean
R_eq_Rg_JInput
R_succ_eq_Rdiamond_JInput
concrete_threshold_core_assumptions :
  Abstract.ThresholdCoreAssumptions R
concrete_main_comparison :
  forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q
```

The concrete main comparison is obtained by applying
`Abstract.main_comparison_from_core` to
`concrete_threshold_core_assumptions`.

`PathCompressionDigestion/PaperConsequences.lean` formalizes the direct
paper-facing consequence:

```lean
theorem direct_paper_consequence
    {z Q r : Nat}
    (hz : 1 <= z)
    (hQ : 1 <= Q)
    (hr : A z (4 * Q) > r) :
    J (z + 1) r <= Q
```

`PathCompressionDigestion/AlphaPrelude.lean` adds generic alpha/least-index
preparation and Ackermann buffer facts. This is preparation for later
paper-specific alpha/cost consequences, not the final paper alpha/cost theorem.

`PathCompressionDigestion/AlphaTail.lean` adds the paper-specific alpha
definition layer: packet `L`, packet `Q`, `alphaQ`, `alphaJQ`, and a
Nat-threshold encoding of `alphaJS`, plus conditional/unconditional bridge
lemmas and the positive-domain source-faithful `alphaJS <= alphaQ + 2`
comparison. It does not formalize the source recurrence/cost theorem.

`PathCompressionDigestion/SourceCost.lean` adds a conditional source-cost
interface and proves the finite paper-facing cost theorem from it:

```lean
theorem source_cost_bound_of_recurrence
    {F : SourceCostFamily}
    (HF : SourceRecurrence F)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    F m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

The source recurrence remains an explicit assumption, not a proved model
theorem.

`PathCompressionDigestion/SourceIteration.lean` adds the pure iteration bridge
from a base source bound and one shifting step per concrete `J` row:

```lean
theorem sourceRecurrence_of_iterated_shifting
    {F : SourceCostFamily}
    (hbase : SourceBound F 0 (J 0))
    (hshift : forall k : Nat, SourceShiftStep F k (JInput k)) :
    SourceRecurrence F
```

`PathCompressionDigestion/SourceModel.lean` packages these obligations in a
structured source interface and derives:

```lean
theorem sourceRecurrence_of_shifting
    (M : SourceModel) :
    SourceRecurrence M.Cost
```

This is not a concrete top-down path-compression model theorem; it identifies
the base and shifting obligations that remain to be instantiated.

`PathCompressionDigestion/ConcreteSourceModel.lean` adds a finite concrete
source-model skeleton beneath that interface. It defines raw ranked forests,
bounded top-down compression paths, compression steps, finite executions,
source-style rootpath/nonrootpath cost, base-rank-accounting certificates, and:

```lean
noncomputable def topDownCost : SourceCostFamily
```

It proves the concrete base obligation for the base-accounted cost family:

```lean
theorem topDown_base_bound :
    topDownBaseBoundTarget
```

It records the remaining Seidel--Sharir shift obligation as a named `Prop`
target:

```lean
def topDownBaseBoundTarget : Prop
def topDownShiftStepTarget (k : Nat) : Prop
def topDownSourceModelTarget : Prop
```

The shift target is not proved or assumed.

`PathCompressionDigestion/PaperPipeline.lean` exposes the direct-proof
pipeline under paper-facing wrapper names, including:

```lean
theorem paper_finite_bound_of_source_recurrence
    {F : SourceCostFamily}
    (HF : SourceRecurrence F)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    F m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

This is the final finite bound in the Lean lane, conditional on the explicit
`SourceRecurrence` interface.

It also exposes the corresponding bound for the structured source-shifting
interface:

```lean
theorem paper_finite_bound_of_source_model
    (M : SourceModel)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    M.Cost m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

The Lean root file `PathCompressionDigestion.lean` imports these concrete
support modules, including `ConcreteCore.lean` and
`ConcreteSourceModel.lean`, along with the Ackermann, threshold, and
main-comparison modules.

## What is intentionally not formalized

The current merged Lean lane still does not prove:

* the derivation of base-rank-accounting certificates from raw source
  executions and the shifting obligation for `ConcreteSourceModel.topDownCost`;
* source anchors or release packaging;
* asymptotic Big-O packaging;
* the unconditional full paper theorem for the actual source model.

The finite object skeleton is present and the base bound is proved for
executions carrying an explicit base-rank-accounting certificate. The match to
the source cost functional, the derivation of that certificate from raw step
semantics, and the combinatorial shift proof remain open. The concrete diamond
transform, recursive concrete `J_k` hierarchy, concrete threshold inverse `R`,
generic diamond-to-threshold recurrence, concrete threshold core assumptions
for `R`, concrete main comparison via `Abstract.main_comparison_from_core`,
generic alpha prelude, paper-specific alpha comparison, and conditional
source-cost consequence are in the Lean lane and should not be marked absent.
The finite paper-facing bound is formalized conditionally, not as an
unconditional theorem about the unproved source model.

## Proof status

The Ackermann package in `PathCompressionDigestion/Ackermann.lean` is now
proof-complete for the four public facts mapped to paper Lemma 4.5 and its
exponential corollary.

The row-domination invariant and main comparison are now proved from
`ThresholdCoreAssumptions R` alone. The concrete maximum definition of
`R_k(t)` is formalized, and `ConcreteCore.lean` now proves that this concrete
`R` satisfies `ThresholdCoreAssumptions` and derives the concrete comparison
`A z (4*Q) <= R (z+1) Q`. `PaperConsequences.lean` now derives the direct
paper consequence `A z (4*Q) > r -> J (z+1) r <= Q`.

The concrete base row, `ceilLog2` support facts, diamond transform, recursive
concrete `J_k` hierarchy, generic threshold-inverse infrastructure, generic
threshold-inverse extras, concrete threshold inverse `R`, generic
diamond-to-threshold recurrence, concrete core bridge, direct paper
consequence, and generic alpha prelude are present as setup for later
paper-specific cost work. The paper-specific alpha definitions, conditional
bridges, and source-faithful `alphaJS <= alphaQ + 2` comparison are present in
`AlphaTail.lean`. The conditional finite cost theorem is present in
`SourceCost.lean`; the source-shifting iteration bridge is present in
`SourceIteration.lean` and `SourceModel.lean`; the concrete finite execution
skeleton, `topDownCost`, and base theorem `topDown_base_bound` are present in
`ConcreteSourceModel.lean`; and the proved bridge results are re-exposed under
paper-facing names in `PaperPipeline.lean`.

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
| `R_eq_Rg_JInput`, `R_succ_eq_Rdiamond_JInput` | Concrete identifications between `R` and the generic `JInput` inverses |
| `concrete_threshold_core_assumptions` | Concrete threshold core assumptions for `R` |
| `concrete_main_comparison` | Concrete main comparison via `Abstract.main_comparison_from_core` |
| `J_le_of_le_R`, `direct_paper_consequence` | Direct paper-facing consequence from the concrete comparison |
| `Abstract.alphaOf` and alpha prelude facts | Generic preparation for later alpha consequences |
| `L`, `Q`, `alphaQ`, `alphaJQ`, `alphaJS`, and AlphaTail bridge/comparison lemmas | Paper-specific alpha-tail layer |
| `SourceCostFamily`, `SourceRecurrence`, `source_cost_bound_of_recurrence` | Conditional source-cost consequence |
| `SourceBound`, `SourceShiftStep`, `sourceBound_J_of_iterated_shifting`, `sourceRecurrence_of_iterated_shifting` | Iteration from source base/shift obligations to `SourceRecurrence` |
| `SourceModel`, `sourceRecurrence_of_shifting`, `source_model_cost_bound` | Structured source-shifting interface and finite cost consequence |
| `RawRankedForest`, `RawCompressionPath`, `RawCompressionStep`, `RawCompressionExecution`, `topDownCost`, `topDown_base_bound`, `topDownShiftStepTarget` | Concrete source-model skeleton, proved base bound for base-accounted executions, and unproved shift target |
| `paper_concrete_main_comparison`, `paper_direct_J_bound`, `paper_alphaJQ_bound`, `paper_alphaJS_bound`, `paper_finite_bound_of_source_recurrence`, `paper_finite_bound_of_source_model` | Paper-facing direct-proof pipeline wrappers |
| `Abstract.ThresholdCoreAssumptions.baseExact` | Section 4.4, exact base inverse |
| `Abstract.ThresholdCoreAssumptions.thresholdStep` | Lemma 4.3 |
| `Abstract.threshold_jump_from_step` | Lemma 4.4 |
| `Abstract.row_domination_invariant` | Lemma 4.6 |
| `Abstract.small_Q_one` | Theorem 4.7, `Q=1` cases |
| `Abstract.main_comparison_from_core` | Theorem 4.7 main comparison |
| `Abstract.MainComparisonAssumptions` / `Abstract.main_comparison` | Legacy wrapper for the original scaffold interface |
