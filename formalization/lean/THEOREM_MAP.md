# Lean Theorem Map and Audit Guide

This document maps the paper/proof-note targets to the current Lean files,
names, and open dependencies. It is an audit guide for future Lean work, not a
new theorem statement and not a claim that the concrete Seidel--Sharir
hierarchy has been fully formalized.

## Repository/checkpoint status

- Base checkpoint audited here:
  `main @ 5d0b1bd39dfbf222ed4c7bb74566a0789a0aef2d`.
- Checkpoint title: `Formalize diamond transform`.
- Current Lean status at this checkpoint: the concrete `g^diamond` transform is
  formalized as a reusable preservation package, but the recursive concrete
  `J_k` hierarchy and concrete `R_k(t)` threshold family are not yet
  formalized.
- Release-layer status: v0.2.1 was a citation/bibliography-rendering patch over
  v0.2.0. It did not change theorem statements, proof constants, Lean
  formalization content, or talk slides from v0.2.0.

The paper/proof-note target remains:

```text
R_{z+1}(Q) >= A(z,4Q)
```

with:

```text
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
```

Any edit touching these normalizations or constants is high risk and is outside
the docs-only scope of this branch.

## Already formalized Lean layers

| Paper/proof target | Lean file | Lean theorem/definition names | Status | Notes / next dependency |
|---|---|---|---|---|
| Packet Ackermann package | `PathCompressionDigestion/Ackermann.lean` | `A`, `A_zero`, `A_succ_zero`, `A_succ_one`, `A_succ_succ`, `Ackermann.monotone_right`, `Ackermann.ge_two_mul`, `Ackermann.row_domination`, `Ackermann.one_eq_pow` | Proved | Matches the packet Ackermann normalization used in paper Lemma 4.5 and the exponentiation corollary. |
| Basic arithmetic helpers | `PathCompressionDigestion/Basic.lean` | `one_or_two_le`, `one_le_four_mul` | Proved | Small support facts for the abstract comparison. |
| Abstract threshold interface | `PathCompressionDigestion/Threshold.lean` | `ThresholdFamily`, `Abstract.thresholdInverseShape`, `Abstract.ThresholdCoreAssumptions`, `Abstract.ThresholdAssumptions` | Defined as an abstract interface | This is the current boundary between abstract Lean and future concrete `R`. No concrete `R` instance is provided here. |
| Abstract threshold jump | `PathCompressionDigestion/Threshold.lean` | `Abstract.four_mul_le_two_pow_two_mul_sub_one`, `Abstract.threshold_jump_from_step`, `Abstract.threshold_jump`, `Abstract.ThresholdAssumptions.ofCore` | Proved from `ThresholdCoreAssumptions` | Corresponds to paper Lemma 4.4. Future work should instantiate `thresholdStep` for concrete `R`, not re-prove the abstract jump. |
| Abstract row domination and main comparison | `PathCompressionDigestion/MainComparison.lean` | `Abstract.row_domination_base`, `Abstract.row_domination_step`, `Abstract.row_domination_invariant_from_core`, `Abstract.small_Q_one_from_core`, `Abstract.MainComparisonAssumptions`, `Abstract.main_comparison`, `Abstract.main_comparison_from_threshold`, `Abstract.main_comparison_from_core` | Proved abstractly | `main_comparison_from_core` proves `forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q` under `ThresholdCoreAssumptions R`. Do not re-prove this theorem. |
| Concrete base row `J_0` | `PathCompressionDigestion/JBase.lean` | `J0`, `J0_zero`, `J0_one`, `J0_two`, `J0_monotone`, `J0_lt_self` | Proved for the base row only | This does not define recursive `J_k`. Next dependency is `JHierarchy`. |
| Base inverse for `J_0` | `PathCompressionDigestion/JBase.lean` | `J0_le_iff_le_two_mul_add_one`, `J0_base_inverse_lower`, `J0_base_inverse_upper`, `J0_base_inverse`, `J0_base_inverse_isGreatest` | Proved | Gives the exact base inverse shape corresponding to `R_0(t) = 2*t + 1`; it is not yet wired into a concrete family `R k t`. |
| `ceilLog2` support | `PathCompressionDigestion/CeilLog2.lean` | `ceilLog2`, `ceilLog2_zero`, `ceilLog2_one`, `ceilLog2_two`, `self_le_two_pow_pred`, `ceilLog2_le_pred`, `ceilLog2_lt_self`, `monotone_ceilLog2`, `le_two_pow_ceilLog2`, `ceilLog2_le_of_le_two_pow` | Proved | Provides termination and monotonicity facts for the diamond recursion. |
| Generic threshold inverse infrastructure | `PathCompressionDigestion/ThresholdInverse.lean` | `ThresholdInverse.Data`, `ThresholdInverse.Data.upperBound`, `ThresholdInverse.thresholdInverse`, `ThresholdInverse.thresholdInverse_le_upperBound`, `ThresholdInverse.le_thresholdInverse_of_apply_le`, `ThresholdInverse.apply_thresholdInverse_le`, `ThresholdInverse.apply_le_of_le_thresholdInverse`, `ThresholdInverse.thresholdInverse_mono_threshold`, `ThresholdInverse.thresholdInverse_mono_function` | Proved generically | This is reusable infrastructure for a future concrete `R_k(t) = max { r : J_k r <= t }`; it does not define `J_k` or concrete `R_k`. |
| Diamond transform and preservation package | `PathCompressionDigestion/Diamond.lean` | `DiamondInput`, `DiamondInput.diamond`, `DiamondInput.ceilLog2_g_lt_of_large`, `DiamondInput.diamond_eq_small`, `DiamondInput.diamond_eq_large`, `DiamondInput.diamond_zero`, `DiamondInput.g_le_self`, `DiamondInput.diamond_le_g`, `DiamondInput.diamond_lt_self_pos`, `DiamondInput.diamond_monotone`, `DiamondInput.lt_ceilLog2_of_pow_lt`, `DiamondInput.diamond_unbounded` | Proved for any `DiamondInput` | Formalizes the reusable `g^diamond` transform. It still needs to be instantiated recursively to build the concrete `J_k` hierarchy. |
| Lean root import surface | `PathCompressionDigestion.lean` | Imports `Basic`, `JBase`, `CeilLog2`, `Diamond`, `Ackermann`, `Threshold`, `ThresholdInverse`, `MainComparison` | Present | Use this file to see the intended public Lean lane. |

## Not yet formalized

The following items are not formalized at this checkpoint:

- Recursive concrete `J_k` hierarchy.
- Concrete `R_k(t) = max { r : J_k r <= t }`.
- Concrete proof that the resulting `R` satisfies
  `ThresholdCoreAssumptions`.
- Concrete main comparison corollary obtained by applying
  `Abstract.main_comparison_from_core` to the concrete `R`.
- Concrete implication
  `A z (4*Q) > r -> J (z+1) r <= Q`.
- Alpha definitions, including packet `alpha_Q`, integer-threshold
  `alpha_J^Q`, and source real-threshold `alpha_J^S`.
- `+1` and `+2` alpha consequences.
- Source recurrence and cost theorem.

In particular, the Lean lane currently proves the abstract comparison under
`ThresholdCoreAssumptions R`; it does not yet prove that the concrete
Seidel--Sharir `J` hierarchy satisfies those assumptions.

## Dependency DAG

```text
Diamond
  -> JHierarchy
  -> ConcreteThreshold
  -> ConcreteCore / ThresholdCoreAssumptions
  -> concrete main comparison
  -> alpha/cost consequences
```

Independent or preparatory branches can be useful when kept narrow:

```text
ThresholdInverseExtras
AlphaPrelude
theorem-map/docs audit
```

Suggested interpretation:

- `Diamond` is now available as the `DiamondInput` preservation package.
- `JHierarchy` should define recursive concrete rows using the diamond package.
- `ConcreteThreshold` should define the concrete maximum inverse using the
  generic threshold inverse infrastructure.
- `ConcreteCore / ThresholdCoreAssumptions` should prove the concrete family
  satisfies the abstract interface fields.
- Only after that should workers state a concrete main comparison corollary.
- Alpha and cost consequences depend on the concrete comparison plus the packet
  alpha definitions and source recurrence.

## Worker guidance

- Do not re-prove `Abstract.main_comparison_from_core`; instantiate it after a
  concrete `R` satisfies `ThresholdCoreAssumptions`.
- Do not define concrete `R` before `JHierarchy` is merged, except in a local
  experimental branch.
- Do not claim full formalization until the concrete `R` has been proved to
  satisfy `ThresholdCoreAssumptions`.
- Do not claim alpha or cost consequences from the current abstract theorem
  alone.
- Do not use `sorry`, `admit`, or `axiom`.
- Do not edit theorem statements or silently change normalizations.
- Always run `lake build` and a source-only scan before and after Lean edits:

```powershell
cd formalization/lean
lake build
Select-String -Path `
  .\PathCompressionDigestion.lean, .\PathCompressionDigestion\*.lean `
  -Pattern '\b(sorry|admit|axiom)\b'
cd ../..
```

For docs-only changes, still run the same build and source scan when feasible,
because the point of this guide is to preserve the Lean lane boundary.
