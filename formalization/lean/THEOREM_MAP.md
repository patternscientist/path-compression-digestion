# Lean Theorem Map and Audit Guide

This document maps the paper/proof-note targets to the current Lean files,
names, and open dependencies. It is an audit guide for future Lean work, not a
new theorem statement and not a claim that the full paper alpha/cost theorem is
formalized.

## Repository/checkpoint status

- Current main HEAD used for this map:
  `c0a122444f14a6ce7729258e92de85c59515d6ad`.
- Recent merged Lean work includes:
  - `lean-j-hierarchy-v1`: formalized the concrete recursive `J_k` hierarchy.
  - `lean-threshold-inverse-extras-v1`: added generic threshold-inverse support
    lemmas.
  - `lean-alpha-prelude-v1`: added generic alpha prelude facts.
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
| Abstract threshold core | `PathCompressionDigestion/Threshold.lean` | `ThresholdFamily`, `Abstract.thresholdInverseShape`, `Abstract.ThresholdCoreAssumptions`, `Abstract.ThresholdAssumptions`, `Abstract.level_monotone_core`, `Abstract.threshold_lower_base`, `Abstract.one_le_threshold_core` | Proved/defined abstractly | This remains the interface a future concrete `R` must satisfy. |
| Abstract threshold jump | `PathCompressionDigestion/Threshold.lean` | `Abstract.four_mul_le_two_pow_two_mul_sub_one`, `Abstract.threshold_jump_from_step`, `Abstract.threshold_step`, `Abstract.threshold_jump`, `Abstract.ThresholdAssumptions.ofCore` | Proved abstractly | Future workers should instantiate `ThresholdCoreAssumptions`, not re-prove this jump. |
| Abstract main comparison | `PathCompressionDigestion/MainComparison.lean` | `Abstract.row_domination_base`, `Abstract.row_domination_step`, `Abstract.row_domination_invariant_from_core`, `Abstract.small_Q_one_from_core`, `Abstract.main_comparison`, `Abstract.main_comparison_from_threshold`, `Abstract.main_comparison_from_core` | Proved abstractly | `main_comparison_from_core` is the theorem to reuse after the concrete core bridge is proved. |
| Base row `J_0` | `PathCompressionDigestion/JBase.lean` | `J0`, `J0_zero`, `J0_one`, `J0_two`, `J0_monotone`, `J0_lt_self` | Proved | Base row only; recursive hierarchy is in `JHierarchy.lean`. |
| Exact base inverse for `J_0` | `PathCompressionDigestion/JBase.lean` | `J0_le_iff_le_two_mul_add_one`, `J0_base_inverse_lower`, `J0_base_inverse_upper`, `J0_base_inverse`, `J0_base_inverse_isGreatest` | Proved | Corresponds to the exact base inverse shape `R_0(t) = 2*t + 1`; concrete `R` is still not defined. |
| `ceilLog2` support | `PathCompressionDigestion/CeilLog2.lean` | `ceilLog2`, `ceilLog2_zero`, `ceilLog2_one`, `ceilLog2_two`, `self_le_two_pow_pred`, `ceilLog2_le_pred`, `ceilLog2_lt_self`, `monotone_ceilLog2`, `le_two_pow_ceilLog2`, `ceilLog2_le_of_le_two_pow` | Proved | Supports the diamond recursion and later threshold recurrence work. |
| Diamond transform | `PathCompressionDigestion/Diamond.lean` | `DiamondInput`, `DiamondInput.diamond`, `DiamondInput.ceilLog2_g_lt_of_large`, `DiamondInput.diamond_eq_small`, `DiamondInput.diamond_eq_large` | Proved | Defines the reusable paper `g^diamond` transform. |
| Diamond preservation package | `PathCompressionDigestion/Diamond.lean` | `DiamondInput.diamond_zero`, `DiamondInput.g_le_self`, `DiamondInput.diamond_le_g`, `DiamondInput.diamond_lt_self_pos`, `DiamondInput.diamond_monotone`, `DiamondInput.lt_ceilLog2_of_pow_lt`, `DiamondInput.diamond_unbounded` | Proved | This is now available to build recursive rows. |
| Recursive concrete `J_k` hierarchy | `PathCompressionDigestion/JHierarchy.lean` | `DiamondInput.next`, `J0_unbounded`, `J0_lt_self_pos`, `J0Input`, `JInput`, `J`, `J_zero_row`, `J_succ_row`, `J_zero_arg` | Proved/defined | Concrete `J_k` is formalized. Do not mark it missing. |
| Basic concrete `J_k` package | `PathCompressionDigestion/JHierarchy.lean` | `J_monotone`, `J_unbounded`, `J_lt_self_pos`, `J_le_self`, `J_succ_le`, `J_level_antitone` | Proved | Supplies the monotonicity, unboundedness, descent, and level-antitone facts needed for concrete threshold inverses. |
| Generic threshold inverse infrastructure | `PathCompressionDigestion/ThresholdInverse.lean` | `ThresholdInverse.Data`, `ThresholdInverse.Data.upperBound`, `ThresholdInverse.Data.upperBound_spec`, `ThresholdInverse.thresholdInverse`, `ThresholdInverse.thresholdInverse_le_upperBound`, `ThresholdInverse.le_thresholdInverse_of_apply_le`, `ThresholdInverse.apply_thresholdInverse_le`, `ThresholdInverse.apply_le_of_le_thresholdInverse`, `ThresholdInverse.thresholdInverse_mono_threshold`, `ThresholdInverse.thresholdInverse_mono_function` | Proved generically | Does not define concrete `R`; use it in a future `ConcreteThreshold.lean`. |
| Generic threshold inverse extras | `PathCompressionDigestion/ThresholdInverseExtras.lean` | `ThresholdInverse.eventually_ge_of_monotone_unbounded`, `ThresholdInverse.eventually_gt_of_monotone_unbounded`, `ThresholdInverse.Data.of_monotone_unbounded`, `ThresholdInverse.thresholdInverse_mono_function_of_monotone_unbounded`, `ThresholdInverse.lt_apply_succ_thresholdInverse` | Proved generically | Constructor and escape lemmas for building concrete threshold inverse data from `J` rows. |
| Generic alpha prelude | `PathCompressionDigestion/AlphaPrelude.lean` | `Ackermann.monotone_left_of_pos`, `Ackermann.eval_two`, `Ackermann.four_mul_column_mono`, `Ackermann.four_mul_column_succ`, `le_four_mul`, `Abstract.alphaOf`, `Abstract.alpha_spec`, `Abstract.alpha_min`, `Abstract.target_le_R_of_le_ackermann_four_mul`, `Abstract.alphaOf_le_succ_of_le_ackermann_four_mul`, `Abstract.alphaOf_le_succ_of_main_comparison_from_core` | Proved generically/preparatory | Useful for later alpha/cost work, but not the final paper-specific alpha or cost theorem. |
| Lean root import surface | `PathCompressionDigestion.lean` | Imports `Basic`, `JBase`, `CeilLog2`, `Diamond`, `JHierarchy`, `Ackermann`, `Threshold`, `ThresholdInverse`, `ThresholdInverseExtras`, `MainComparison`, `AlphaPrelude` | Present | This is the current public Lean lane. |

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
- Generic alpha prelude.

## Not yet formalized

The following items remain open at this checkpoint:

- Concrete threshold inverse family:
  `R k t = max { r : J k r <= t }`. Likely next file:
  `ConcreteThreshold.lean`.
- Proof that concrete `R` satisfies `ThresholdCoreAssumptions`, including:
  base exactness for concrete `R`, threshold monotonicity, level monotonicity,
  and the threshold-step / diamond-to-threshold recurrence.
- Concrete main comparison corollary, obtained by applying
  `Abstract.main_comparison_from_core` after the concrete core assumptions are
  proved.
- Direct paper consequence:
  `A z (4*Q) > r -> J (z+1) r <= Q`.
- Full paper alpha/cost tail:
  paper-specific `L(n)`, integer `Q(m,n)`, concrete `alpha_Q`,
  `alpha_J^Q`, `alpha_J^S`, the `+1/+2` concrete alpha consequences, and the
  source recurrence/cost theorem.
- Source Seidel--Sharir recurrence itself as a full formal cost theorem.

In particular, `AlphaPrelude.lean` is generic preparation. It does not by
itself formalize the paper-specific alpha definitions or cost consequences.

## Dependency DAG

```text
Diamond ✅
  -> JHierarchy ✅
  -> ConcreteThreshold / concrete R ⬜
  -> ConcreteCore / ThresholdCoreAssumptions concreteR ⬜
  -> concrete main comparison corollary ⬜
  -> paper-specific alpha/cost consequences ⬜

ThresholdInverseExtras ✅
  -> ConcreteThreshold

AlphaPrelude ✅
  -> paper-specific alpha/cost consequences

TheoremMap/docs audit
  -> worker coordination
```

## Worker guidance

- Do not re-prove `Abstract.main_comparison_from_core`; reuse it after the
  concrete `R` bridge is established.
- Do not claim full concrete formalization until concrete `R` satisfies
  `ThresholdCoreAssumptions`.
- The next critical path branch should be concrete `R` /
  `ConcreteThreshold.lean`.
- Do not claim paper alpha/cost consequences from `AlphaPrelude.lean` alone.
- Do not use `sorry`, `admit`, or `axiom`.
- Use targeted module checks for docs-only branches instead of forcing a full
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

For docs-only work, if `lake build PathCompressionDigestion` starts rebuilding
large dependency slices and becomes impractical, report that honestly and rely
on targeted elaboration/source scans when they succeed.
