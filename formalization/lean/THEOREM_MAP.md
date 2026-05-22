# Lean Theorem Map and Audit Guide

This document maps the paper/proof-note targets to the current Lean files,
names, and open dependencies. It is an audit guide for future Lean work, not a
new theorem statement and not a claim that the full paper alpha/cost theorem is
formalized.

## Repository/checkpoint status

- Current main checkpoint fetched before this update:
  `a742bb89c768645ae17943604c578693b3cad94a`.
- Recent merged Lean work available at this checkpoint includes:
  - `lean-concrete-core-v1`: added `ConcreteCore.lean`, proving the concrete
    threshold core assumptions for `R` and the concrete main comparison via
    `Abstract.main_comparison_from_core`.
  - `lean-direct-paper-consequence-v1`: added `PaperConsequences.lean`,
    proving the direct paper-facing implication
    `A z (4 * Q) > r -> J (z + 1) r <= Q`.
  - `lean-concrete-threshold-v1`: defined the concrete threshold inverse `R`
    for the `J` hierarchy and proved its base, threshold-monotonicity,
    level-monotonicity, and inverse/spec wrappers.
  - `lean-diamond-threshold-step-v1`: proved the generic
    diamond-to-threshold recurrence for a `DiamondInput`.
  - `lean-j-hierarchy-v1`: formalized the concrete recursive `J_k` hierarchy.
  - `lean-threshold-inverse-extras-v1`: added generic threshold-inverse support
    lemmas.
  - `lean-alpha-prelude-v1`: added generic alpha prelude facts.
  - `lean-alpha-js-plus-two-v1`: proved the positive-domain
    source-faithful `alphaJS <= alphaQ + 2` comparison.
  - `lean-source-cost-interface-v1`: added `SourceCost.lean`, proving the
    finite cost bound conditional on a `SourceRecurrence` interface.
  - `lean-source-recurrence-model-v1`: added `SourceIteration.lean` and
    `SourceModel.lean`, deriving `SourceRecurrence` from explicit source
    base and shifting obligations rather than assuming it directly.
  - `lean-concrete-source-model-v1`: added `ConcreteSourceModel.lean`, a
    finite top-down source-model skeleton with raw ranked forests, compression
    paths/steps/executions, an extremal `topDownCost`, and named `Prop`
    targets for the concrete base and shift obligations. It proves the base
    bound for base-accounted executions; the shift obligation remains open.
- Earlier checkpoint `5d0b1bd39dfbf222ed4c7bb74566a0789a0aef2d`
  formalized the diamond transform.
- Release-layer status: v0.2.1 was a citation/bibliography-rendering patch over
  v0.2.0. It did not change theorem statements, proof constants, Lean
  formalization content, or talk slides from v0.2.0.

The paper/proof-note comparison target remains:

```text
R_{z+1}(Q) >= A(z,4Q)
```

with:

```text
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
```

Any edit touching these normalizations or constants is high risk.

## Lean module map

| Layer / paper target | Lean file | Definition/theorem names | Status | Notes / next dependency |
|---|---|---|---|---|
| Basic arithmetic helpers | `PathCompressionDigestion/Basic.lean` | `one_or_two_le`, `one_le_four_mul` | Proved | Small shared facts for the comparison lane. |
| Packet Ackermann package | `PathCompressionDigestion/Ackermann.lean` | `A`, `A_zero`, `A_succ_zero`, `A_succ_one`, `A_succ_succ`, `Ackermann.monotone_right`, `Ackermann.ge_two_mul`, `Ackermann.row_domination`, `Ackermann.one_eq_pow` | Proved | Covers the packet Ackermann normalization and paper Lemma 4.5-style facts. |
| Abstract threshold core | `PathCompressionDigestion/Threshold.lean` | `ThresholdFamily`, `Abstract.thresholdInverseShape`, `Abstract.ThresholdCoreAssumptions`, `Abstract.ThresholdAssumptions`, `Abstract.level_monotone_core`, `Abstract.threshold_lower_base`, `Abstract.one_le_threshold_core` | Proved/defined abstractly | This is the interface now satisfied by the concrete `R` in `ConcreteCore.lean`. |
| Abstract threshold jump | `PathCompressionDigestion/Threshold.lean` | `Abstract.four_mul_le_two_pow_two_mul_sub_one`, `Abstract.threshold_jump_from_step`, `Abstract.threshold_step`, `Abstract.threshold_jump`, `Abstract.ThresholdAssumptions.ofCore` | Proved abstractly | `ConcreteCore.lean` instantiates the core assumptions; future work should not re-prove this jump. |
| Abstract main comparison | `PathCompressionDigestion/MainComparison.lean` | `Abstract.row_domination_base`, `Abstract.row_domination_step`, `Abstract.row_domination_invariant_from_core`, `Abstract.small_Q_one_from_core`, `Abstract.main_comparison`, `Abstract.main_comparison_from_threshold`, `Abstract.main_comparison_from_core` | Proved abstractly | `main_comparison_from_core` is reused by the concrete bridge. |
| Base row `J_0` | `PathCompressionDigestion/JBase.lean` | `J0`, `J0_zero`, `J0_one`, `J0_two`, `J0_monotone`, `J0_lt_self` | Proved | Base row only; recursive hierarchy is in `JHierarchy.lean`. |
| Exact base inverse for `J_0` | `PathCompressionDigestion/JBase.lean` | `J0_le_iff_le_two_mul_add_one`, `J0_base_inverse_lower`, `J0_base_inverse_upper`, `J0_base_inverse`, `J0_base_inverse_isGreatest` | Proved | Corresponds to the exact base inverse shape `R_0(t) = 2*t + 1`; used by `ConcreteThreshold.R_zero_eq`. |
| `ceilLog2` support | `PathCompressionDigestion/CeilLog2.lean` | `ceilLog2`, `ceilLog2_zero`, `ceilLog2_one`, `ceilLog2_two`, `self_le_two_pow_pred`, `ceilLog2_le_pred`, `ceilLog2_lt_self`, `monotone_ceilLog2`, `le_two_pow_ceilLog2`, `ceilLog2_le_of_le_two_pow` | Proved | Supports the diamond recursion and later threshold recurrence work. |
| Diamond transform | `PathCompressionDigestion/Diamond.lean` | `DiamondInput`, `DiamondInput.diamond`, `DiamondInput.ceilLog2_g_lt_of_large`, `DiamondInput.diamond_eq_small`, `DiamondInput.diamond_eq_large` | Proved | Defines the reusable paper `g^diamond` transform. |
| Diamond preservation package | `PathCompressionDigestion/Diamond.lean` | `DiamondInput.diamond_zero`, `DiamondInput.g_le_self`, `DiamondInput.diamond_le_g`, `DiamondInput.diamond_lt_self_pos`, `DiamondInput.diamond_monotone`, `DiamondInput.lt_ceilLog2_of_pow_lt`, `DiamondInput.diamond_unbounded` | Proved | This is now available to build recursive rows. |
| Recursive concrete `J_k` hierarchy | `PathCompressionDigestion/JHierarchy.lean` | `DiamondInput.next`, `J0_unbounded`, `J0_lt_self_pos`, `J0Input`, `JInput`, `J`, `J_zero_row`, `J_succ_row`, `J_zero_arg` | Proved/defined | Concrete `J_k` is formalized. Do not mark it missing. |
| Basic concrete `J_k` package | `PathCompressionDigestion/JHierarchy.lean` | `J_monotone`, `J_unbounded`, `J_lt_self_pos`, `J_le_self`, `J_succ_le`, `J_level_antitone` | Proved | Supplies the monotonicity, unboundedness, descent, and level-antitone facts needed for concrete threshold inverses. |
| Generic threshold inverse infrastructure | `PathCompressionDigestion/ThresholdInverse.lean` | `ThresholdInverse.Data`, `ThresholdInverse.Data.upperBound`, `ThresholdInverse.Data.upperBound_spec`, `ThresholdInverse.thresholdInverse`, `ThresholdInverse.thresholdInverse_le_upperBound`, `ThresholdInverse.le_thresholdInverse_of_apply_le`, `ThresholdInverse.apply_thresholdInverse_le`, `ThresholdInverse.apply_le_of_le_thresholdInverse`, `ThresholdInverse.thresholdInverse_mono_threshold`, `ThresholdInverse.thresholdInverse_mono_function` | Proved generically | Used by `ConcreteThreshold.lean` and `DiamondThreshold.lean`. |
| Generic threshold inverse extras | `PathCompressionDigestion/ThresholdInverseExtras.lean` | `ThresholdInverse.eventually_ge_of_monotone_unbounded`, `ThresholdInverse.eventually_gt_of_monotone_unbounded`, `ThresholdInverse.Data.of_monotone_unbounded`, `ThresholdInverse.thresholdInverse_mono_function_of_monotone_unbounded`, `ThresholdInverse.lt_apply_succ_thresholdInverse` | Proved generically | Constructor and escape lemmas used by concrete threshold inverse data from `J` rows and by diamond-threshold data. |
| Concrete threshold inverse family | `PathCompressionDigestion/ConcreteThreshold.lean` | `JThresholdData`, `R`, `J_R_le`, `le_R_of_J_le`, `lt_J_of_R_lt`, `R_monotone_threshold`, `R_mono_t`, `R_monotone_level`, `R_zero_eq` | Proved | Concrete `R k t = max { r : J k r <= t }` is formalized and consumed by `ConcreteCore.lean`. |
| Generic diamond-to-threshold recurrence | `PathCompressionDigestion/DiamondThreshold.lean` | `DiamondInput.gThresholdData`, `DiamondInput.diamondThresholdData`, `DiamondInput.Rg`, `DiamondInput.Rdiamond`, `DiamondInput.threshold_step` | Proved generically | Supplies the threshold-step field after specialization to `JInput k`. |
| Concrete core bridge | `PathCompressionDigestion/ConcreteCore.lean` | `R_eq_Rg_JInput`, `R_succ_eq_Rdiamond_JInput`, `concrete_threshold_core_assumptions`, `concrete_main_comparison` | Proved | Proves `Abstract.ThresholdCoreAssumptions R` and derives `forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q` via `Abstract.main_comparison_from_core`. |
| Direct paper consequence | `PathCompressionDigestion/PaperConsequences.lean` | `J_le_of_le_R`, `direct_paper_consequence` | Proved | Derives `A z (4 * Q) > r -> J (z + 1) r <= Q` from `concrete_main_comparison` and the concrete threshold inverse bridge. |
| Generic alpha prelude | `PathCompressionDigestion/AlphaPrelude.lean` | `Ackermann.monotone_left_of_pos`, `Ackermann.eval_two`, `Ackermann.four_mul_column_mono`, `Ackermann.four_mul_column_succ`, `le_four_mul`, `Abstract.alphaOf`, `Abstract.alpha_spec`, `Abstract.alpha_min`, `Abstract.target_le_R_of_le_ackermann_four_mul`, `Abstract.alphaOf_le_succ_of_le_ackermann_four_mul`, `Abstract.alphaOf_le_succ_of_main_comparison_from_core` | Proved generically/preparatory | Useful for later alpha/cost work, but not the final paper-specific alpha or cost theorem. |
| Paper-specific alpha tail | `PathCompressionDigestion/AlphaTail.lean` | `ceilDiv`, `L`, `Q`, `sourceThreshold`, `ackermannAlphaFamily`, `alphaQ`, `alphaJQ`, `alphaJS`, `alphaQExists`, `one_le_Q`, `one_le_L`, `one_le_alphaQ`, `alphaQ_exists`, `sourceThreshold_le_Q`, `sourceThreshold_le_Q_pos`, `Q_le_sourceThreshold_add_one_pos`, `R_threshold_succ_le_level_succ_threshold`, `alphaQ_spec`, `alphaJQ_le_succ_of_ackermann_witness`, `alphaJQ_exists`, `alphaJQ_le_alphaQ_add_one`, `alphaJQ_le_alphaQ_add_one_unconditional`, `alphaJS_le_alphaJQ_add_one_pos`, `alphaJS_le_alphaQ_add_two`, `alphaJS_eq_alphaJQ_of_sourceThreshold_eq_Q`, `alphaJS_le_alphaQ_add_one_of_sourceThreshold_eq_Q` | Proved/defined, including unconditional existence for `alphaQ`, the unconditional `alphaJQ <= alphaQ + 1` comparison, and the positive-domain source-faithful `alphaJS <= alphaQ + 2` comparison | Defines the paper-specific packet alpha quantities and source-threshold alpha bridge. It does not formalize the source recurrence/cost theorem. |
| Conditional source-cost interface | `PathCompressionDigestion/SourceCost.lean` | `SourceCostFamily`, `SourceRecurrence`, `two_mul_n_mul_Q_le_two_mul_m_add_four_mul_n`, `source_cost_bound_of_recurrence` | Proved conditionally | Isolates the source recurrence as an explicit interface assumption and proves the finite paper-facing cost theorem from it. |
| Source-shifting iteration bridge | `PathCompressionDigestion/SourceIteration.lean` | `SourceBound`, `SourceShiftStep`, `sourceBound_J_of_iterated_shifting`, `sourceRecurrence_of_iterated_shifting` | Proved from base/shift obligations | Proves by induction that a base bound at `J_0` plus the source shifting step along `JInput k` implies `SourceRecurrence`. It does not prove those source obligations for a concrete path-compression model. |
| Structured source model interface | `PathCompressionDigestion/SourceModel.lean` | `SourceModel`, `sourceRecurrence_of_shifting`, `source_model_cost_bound` | Proved for any packaged source base/shift model | Removes direct dependence on `SourceRecurrence` for clients that can supply the base and shifting fields. It is not an unconditional top-down model theorem. |
| Concrete source-model skeleton | `PathCompressionDigestion/ConcreteSourceModel.lean` | `RawRankedForest`, `RawCompressionPath`, `RawCompressionStep`, `RawCompressionExecution`, `RawCompressionExecution.HasBaseRankAccounting`, `topDownCost`, `topDownCost_le_base_budget`, `topDown_base_bound`, `topDown_base_sourceBound`, `topDownShiftStepTarget`, `topDown_sourceModel_of_shift`, `sourceRecurrence_topDownCost_of_shift`, `paper_finite_bound_topDownCost_of_shift` | Base obligation proved for base-accounted executions; full pipeline conditional on shift; shift open | Defines finite ranked-forest/path-compression execution objects and a concrete `SourceCostFamily`. The base bound `SourceBound topDownCost 0 (J 0)` is proved from explicit base-rank-accounting certificates; deriving those certificates from raw step semantics and proving the Seidel--Sharir shift remain open. Conditional wrappers show the full A-shaped pipeline follows from the shift theorem alone. |
| Paper-facing pipeline wrapper | `PathCompressionDigestion/PaperPipeline.lean` | `paper_concrete_main_comparison`, `paper_direct_J_bound`, `paper_alphaJQ_bound`, `paper_alphaJS_bound`, `paper_finite_bound_of_source_recurrence`, `paper_finite_bound_of_source_model` | Proved conditionally for the finite cost bound and proved for structured source models | Exposes the formalized direct-proof pipeline under paper-facing names. The actual top-down path-compression model remains uninstantiated. |
| Lean root import surface | `PathCompressionDigestion.lean` | Imports `Basic`, `JBase`, `CeilLog2`, `Diamond`, `JHierarchy`, `Ackermann`, `Threshold`, `ThresholdInverse`, `ThresholdInverseExtras`, `ConcreteThreshold`, `DiamondThreshold`, `MainComparison`, `ConcreteCore`, `PaperConsequences`, `AlphaPrelude`, `AlphaTail`, `SourceCost`, `SourceIteration`, `SourceModel`, `ConcreteSourceModel`, `PaperPipeline` | Present | This is the current public Lean lane. |

## Already formalized layers

- Packet Ackermann package.
- `ThresholdCoreAssumptions` abstract interface.
- Abstract threshold jump from the primitive core assumptions.
- Abstract row-domination and main comparison from
  `ThresholdCoreAssumptions`.
- Base `J0` and exact base inverse facts.
- `ceilLog2` support.
- Diamond transform and preservation facts.
- Recursive concrete `J_k` hierarchy and its basic package.
- Generic threshold inverse infrastructure.
- Generic threshold inverse extras.
- Concrete threshold inverse `R` for the `J` hierarchy.
- Generic diamond-to-threshold recurrence for a `DiamondInput`.
- Concrete threshold core assumptions for `R`.
- Concrete main comparison via `Abstract.main_comparison_from_core`.
- Direct paper consequence `A z (4*Q) > r -> J (z+1) r <= Q`.
- Generic alpha prelude.
- Paper-specific alpha definitions, alphaQ existence, and source-faithful
  `alphaJS <= alphaQ + 2` comparison.
- Conditional source-cost interface and finite cost theorem
  `source_cost_bound_of_recurrence`.
- Source-shifting iteration bridge
  `sourceRecurrence_of_iterated_shifting`, deriving `SourceRecurrence` from a
  base bound and per-level source shifting steps along the concrete `J`
  hierarchy.
- Structured source interface theorem `sourceRecurrence_of_shifting` and
  finite model-wrapper theorem `source_model_cost_bound`.
- Concrete source-model skeleton with finite ranked forests, top-down
  compression paths/steps/executions, and `topDownCost`; the base source
  obligation `topDown_base_sourceBound` is proved for base-accounted
  executions, and the finite paper bound is available conditional on the
  remaining shift theorem.
- Paper-facing pipeline wrappers, including
  `paper_finite_bound_of_source_recurrence` and
  `paper_finite_bound_of_source_model`.

## Not yet formalized

The following items remain open at this checkpoint:

- Concrete source/top-down path-compression model theorem, including proofs of
  the base-rank-accounting certificate from raw step semantics and the
  shifting obligation for `ConcreteSourceModel.topDownCost`.
- Asymptotic Big-O packaging.
- Unconditional full paper theorem for the actual source path-compression
  model.

In particular, `AlphaPrelude.lean` is generic preparation. The paper-specific
alpha definitions and alpha comparison live in `AlphaTail.lean`; the finite
cost consequence conditional on a `SourceRecurrence` interface lives in
`SourceCost.lean` and is re-exposed in `PaperPipeline.lean`.

## Dependency DAG

```text
Diamond complete
  -> JHierarchy complete
  -> ConcreteThreshold complete
  -> ConcreteCore / ThresholdCoreAssumptions R complete
  -> concrete main comparison via Abstract.main_comparison_from_core complete
  -> direct paper consequence complete
  -> paper-specific alpha comparison complete
  -> source-shifting iteration bridge complete
  -> concrete source-model skeleton present, base obligation complete,
     shift obligation open
  -> conditional/structured source-cost theorem complete
  -> paper-facing wrapper complete

DiamondThreshold complete
  -> ConcreteCore complete

ThresholdInverseExtras complete
  -> ConcreteThreshold

AlphaPrelude complete
  -> AlphaTail paper-specific alpha definition layer, alphaQ existence,
     unconditional alphaJQ/alphaQ comparison, and source-faithful
     alphaJS/alphaQ +2 comparison
  -> SourceCost conditional finite cost theorem
  -> SourceIteration / SourceModel source-shifting bridge
  -> ConcreteSourceModel finite execution skeleton
  -> PaperPipeline final conditional wrapper

TheoremMap/docs audit
  -> worker coordination
```

## Worker guidance

- Do not re-prove `Abstract.main_comparison_from_core`; the concrete
  comparison already reuses it through `ConcreteCore.lean`.
- Do not claim paper alpha/cost consequences from the concrete comparison or
  direct paper consequence alone.
- Do not claim paper alpha/cost consequences from `AlphaPrelude.lean` alone.
- Do not use `sorry`, `admit`, or `axiom`.
- For docs-only branches, run `git diff --check` and the source-only
  `sorry`/`admit`/`axiom` scan.
- Use targeted module checks for Lean source branches instead of forcing a full
  Mathlib rebuild every time.
- Before and after Lean source changes, run at least:

```powershell
cd formalization/lean
lake build PathCompressionDigestion
lake env lean PathCompressionDigestion.lean
Select-String -Path `
  .\PathCompressionDigestion.lean, .\PathCompressionDigestion\*.lean `
  -Pattern '\b(sorry|admit|axiom)\b'
cd ../..
```

For docs-only work, do not force a full Mathlib rebuild. Reserve broad builds
for release preparation or explicit Lean-source validation.
