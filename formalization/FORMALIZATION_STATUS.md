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

For the current source-recurrence/model boundary, see:

- `formalization/lean/SOURCE_RECURRENCE_MODEL_STATUS.md`

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
- `formalization/lean/PathCompressionDigestion/ConcreteCore.lean` identifies
  the concrete `R` with the generic inverse families for `JInput`, proves the
  concrete threshold core assumptions for `R`, and derives the concrete main
  comparison from the abstract theorem.
- `formalization/lean/PathCompressionDigestion/PaperConsequences.lean`
  formalizes the direct paper-facing consequence
  `A z (4 * Q) > r -> J (z + 1) r <= Q`.
- `formalization/lean/PathCompressionDigestion/AlphaPrelude.lean` provides
  generic alpha/least-index preparation and Ackermann buffer facts. It is not
  the final paper-specific alpha/cost formalization.
- `formalization/lean/PathCompressionDigestion/AlphaTail.lean` defines the
  paper-specific alpha-tail layer: `L`, `Q`, `alphaQ`, `alphaJQ`, and a
  Nat-threshold encoding of `alphaJS`, plus conditional/unconditional bridge
  lemmas and the positive-domain source-faithful `alphaJS <= alphaQ + 2`
  comparison.
- `formalization/lean/PathCompressionDigestion/SourceCost.lean` defines a
  conditional `SourceRecurrence` interface and proves the finite paper-facing
  cost theorem from that interface. It does not formalize the source
  recurrence/model itself.
- `formalization/lean/PathCompressionDigestion/SourceIteration.lean` proves
  that a source base bound at `J_0` plus one source shifting step for each
  concrete `J_k` row implies the existing `SourceRecurrence` interface.
- `formalization/lean/PathCompressionDigestion/SourceModel.lean` packages the
  source base and shifting obligations as a structured interface and derives
  both `SourceRecurrence` and the finite cost bound for any such model.
- `formalization/lean/PathCompressionDigestion/ConcreteSourceModel.lean`
  defines a finite concrete source-model skeleton beneath `SourceModel`:
  ranked forests over `Fin n`, bounded compression paths, compression steps,
  finite executions, source-style rootpath/nonrootpath cost,
  base-rank-accounting certificates, direct rank-threshold packing, and
  `topDownCost : SourceCostFamily`. It proves the base obligation for this
  base-accounted cost family; the certificate derivation from raw step
  semantics and the shifting obligation remain open. It also provides
  conditional wrappers showing that
  `SourceModel`, `SourceRecurrence topDownCost`, and the finite paper-facing
  bound follow from the remaining shift theorem.
- `formalization/lean/PathCompressionDigestion/SourceDissection.lean` and
  `formalization/lean/PathCompressionDigestion/SourceProjection.lean` add the
  dissection/projection layer beneath the shift target.  The current repair
  derives rank-threshold `TopPacking` from the new direct rank-packing
  invariant and preserves the old one-vertex high-rank-root obstruction only
  for a legacy-without-packing predicate.  The projection layer also proves
  rank-range bounds for charged rank-threshold projections: bottom consumable
  cost is bounded by `s` per charged bottom projection, and top consumable cost
  is bounded by `r - s - 1` per charged top projection. Direct rank-packing is
  also proved to localize to the rank-threshold bottom side.
- `formalization/lean/PathCompressionDigestion/PaperPipeline.lean` exposes the
  formalized direct-proof pipeline under paper-facing wrapper names, including
  the finite bound conditional on `SourceRecurrence` and the corresponding
  finite bound for a structured source-shifting model.
- `formalization/lean/PathCompressionDigestion.lean` imports these concrete
  support modules along with the abstract comparison modules.

## Proved in Lean

- The packet Ackermann package in
  `formalization/lean/PathCompressionDigestion/Ackermann.lean`.
- The abstract threshold engine in
  `formalization/lean/PathCompressionDigestion/Threshold.lean`, including
  `ThresholdCoreAssumptions` and the threshold jump derived from it.
- Abstract row-domination and main comparison from `ThresholdCoreAssumptions` in
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
- The concrete core bridge in
  `formalization/lean/PathCompressionDigestion/ConcreteCore.lean`, including
  `R_eq_Rg_JInput`, `R_succ_eq_Rdiamond_JInput`,
  `concrete_threshold_core_assumptions`, and `concrete_main_comparison`.
- The concrete threshold core assumptions for `R` and the concrete main
  comparison
  `forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q`, obtained via
  `Abstract.main_comparison_from_core`.
- The direct paper-facing consequence
  `A z (4 * Q) > r -> J (z + 1) r <= Q`.
- Generic/preparatory alpha prelude facts in
  `formalization/lean/PathCompressionDigestion/AlphaPrelude.lean`.
- The paper-specific alpha-tail definitions, `alphaQ` existence,
  conditional/unconditional `alphaJQ <= alphaQ + 1` bridges, and the
  positive-domain source-faithful `alphaJS <= alphaQ + 2` comparison in
  `formalization/lean/PathCompressionDigestion/AlphaTail.lean`.
- The conditional source-cost interface and finite cost theorem
  `source_cost_bound_of_recurrence` in
  `formalization/lean/PathCompressionDigestion/SourceCost.lean`.
- The source-shifting iteration bridge
  `sourceRecurrence_of_iterated_shifting` in
  `formalization/lean/PathCompressionDigestion/SourceIteration.lean`.
- The structured source-shifting interface theorem
  `sourceRecurrence_of_shifting` and finite cost theorem
  `source_model_cost_bound` in
  `formalization/lean/PathCompressionDigestion/SourceModel.lean`.
- The concrete source-model skeleton definitions in
  `formalization/lean/PathCompressionDigestion/ConcreteSourceModel.lean`,
  including `topDownCost`, `topDownCost_le_base_budget`,
  `topDown_base_bound`, `topDown_base_sourceBound`, and the named remaining
  target `topDownShiftStepTarget`. Faithful base/rank accounting now includes
  direct rank-threshold packing, ruling out the old one-vertex high-rank-root
  model defect. This proves the base field needed by `SourceModel` for
  base-accounted executions, and includes conditional wrappers
  `topDown_sourceModel_of_shift`,
  `sourceRecurrence_topDownCost_of_shift`, and
  `paper_finite_bound_topDownCost_of_shift`. It does not prove the shift field
  or an unconditional concrete `SourceModel`.
- The rank-threshold top-packing field needed by the projected shift package is
  now constructible from the faithful model's direct rank-threshold packing.
  The bottom and top projected consumable costs are now bounded by their side
  rank ranges per charged projected step. The sharper recurrence-consumption
  fields with coefficients `k + 1` and `k` plus side-cardinality budgets remain
  open. Direct rank-threshold packing also localizes to the bottom side,
  giving the bottom-side cardinality invariant needed for a future restricted
  bottom simulation/comparison theorem.
- The paper-facing pipeline wrappers, including
  `paper_finite_bound_of_source_recurrence` and
  `paper_finite_bound_of_source_model`, in
  `formalization/lean/PathCompressionDigestion/PaperPipeline.lean`.
- The concrete base-row facts and generic infrastructure listed above.

## Not Yet Proved in Lean

- A concrete source/top-down path-compression model theorem, including proofs
  that raw valid executions admit the strengthened base/rank-accounting
  certificate and the shifting obligation for `ConcreteSourceModel.topDownCost`.
- Asymptotic Big-O packaging.
- The unconditional full paper theorem for the actual source
  path-compression model.

The finite paper-facing bound is formalized conditional on
`SourceRecurrence`, and also for any structured source model satisfying the
base and shifting obligations. The Lean lane now has a finite concrete
execution skeleton and `topDownCost`, and it proves the base bound for
base-accounted executions. It does not yet derive those accounting
certificates from raw compression semantics or prove the Seidel--Sharir shift
obligation, so it still does not derive an unconditional theorem for the actual
top-down path-compression source model.

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
