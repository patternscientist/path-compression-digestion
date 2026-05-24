# JInput Consumable Bounds Failure Report

Branch: `lean-jinput-consumable-bounds-v1`

Starting base:

```text
local main = a654d2c7d7de867171f98479ab723f4649d4c623
requested prerequisite present = f985c442e995ecaa514ed4e680118993c8348c20
fetched origin/main = 85a1794b14e7d1c964f610312d0ec3833accba44
```

## Summary

This worker did not prove:

```lean
theorem rankThresholdLogConsumableBounds_JInput :
    forall k : Nat,
      RawCompressionExecution.RankThresholdLogConsumableBounds (JInput k) k
```

and therefore did not prove:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

The generic arithmetic bridge remains intact:

```lean
theorem RawCompressionExecution.topDown_shift_step_of_rankThreshold_log_consumable_bounds
    (k : Nat)
    (hconsume : RankThresholdLogConsumableBounds (JInput k) k) :
    topDownShiftStepTarget k
```

The package is already specialized at the bridge boundary. The remaining gap is
the concrete `JInput` proof of the two consumable-cost simulation fields.

## Exact Field Blocked By Delayed Rows

The delayed-row diagnostic blocks the top consumable-cost simulation field of
`RankThresholdLogConsumableBounds`:

```lean
(E.canonicalTopProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
    k *
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
      2 *
        ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
        Drow.g (r - s - 1)
```

For `delayedSubThreeInput` at `r = 6`, the logarithmic threshold is
`s = 2`, but the residual row value vanishes:

```lean
delayedSubThreeInput.g
  (6 - ceilLog2 (delayedSubThreeInput.g 6) - 1) = 0
```

The local audit theorem

```lean
theorem exists_valid_step_with_positive_top_consumable_at_delayed_zero_residual
```

exhibits a valid rank-threshold top projection with one consumable top edge at
that zero residual. Thus, at `k = 0`, the top field has a positive left side
while both terms on the right side can collapse to zero. The current diagnostic
is local-step level; it identifies the exact failed field but stops short of an
execution-level refutation of the whole package.

## Concrete JInput Fact Proved

The delayed obstruction does not occur for the concrete `J` rows. This branch
proved in `JHierarchy.lean`:

```lean
@[simp] theorem J_two_arg (k : Nat) :
    J k 2 = 1

theorem J_pos_of_two_le (k : Nat) {r : Nat} (hr : 2 <= r) :
    0 < J k r

theorem J_large_residual_two_le (k r : Nat) (hlarge : 1 < J k r) :
    2 <= r - ceilLog2 (J k r) - 1

theorem JInput_top_residual_pos_of_large
    (k r : Nat) (hlarge : 1 < (JInput k).g r) :
    0 < (JInput k).g (r - ceilLog2 ((JInput k).g r) - 1)
```

The last theorem is the concrete row-strength fact expected to block the
delayed top-residual counterexample: in the large-row case, `JInput k` always
has a positive residual row after the logarithmic top cut.

## Current Blocker Classification

The blocker is not top packing. The repaired faithful model already supplies:

```lean
noncomputable def RawCompressionExecution.rankThresholdDissectionFamily_topPacking
```

The blocker is also not the downstream shift arithmetic. Once top packing and
the two consumable simulation fields are supplied, Lean already proves the
source shift step through:

```lean
theorem RawCompressionExecution.rankThreshold_source_cost_le_diamond_budget_of_log_consumable_bounds
theorem RawCompressionExecution.sourceShiftStep_of_rankThreshold_log_consumable_bounds
theorem RawCompressionExecution.topDown_shift_step_of_rankThreshold_log_consumable_bounds
```

The precise remaining blocker is execution-level consumable simulation:

- bottom consumable simulation with coefficient `k + 1`;
- top consumable simulation with coefficient `k`;
- charged-count bookkeeping inside the restricted projected executions.

The existing range lemmas

```lean
rankThresholdBottomProjectedExecution_consumableCost_le_threshold_mul_chargedCount
rankThresholdTopProjectedExecution_consumableCost_le_shiftedRank_mul_chargedCount
```

are only rank-range bounds. They do not turn the projected bottom/top slot
families into source-valid restricted executions to which the previous
`topDownCost` recurrence can be applied.

## Package Boundary Recommendation

Preserve `RankThresholdLogConsumableBounds` as the exact arithmetic interface
consumed by the existing bridge, but do not try to prove it from bare
`DiamondInput` row hypotheses. The theorem that should be proved next is the
concrete specialization:

```lean
theorem rankThresholdLogConsumableBounds_JInput :
    forall k : Nat,
      RawCompressionExecution.RankThresholdLogConsumableBounds (JInput k) k
```

If a named concrete package is preferred, it should be definitionally no weaker
than the two consumable fields plus the existing top-packing witness, and the
bridge should immediately reduce to the already-proved arithmetic bridge.

## Smallest Next Theorem Statements

Top side:

```lean
theorem rankThreshold_top_consumableCost_le_JInput_recurrence_budget
    (k : Nat)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := { val := 0, isLt := by omega }
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        k *
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 *
            ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
            (JInput k).g (r - s - 1)
```

Bottom side:

```lean
theorem rankThreshold_bottom_consumableCost_le_JInput_recurrence_budget
    (k : Nat)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := { val := 0, isLt := by omega }
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        (k + 1) *
          (E.canonicalBottomProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 *
            ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
            (JInput k).diamond s
```

These are the smallest concrete fields needed to prove
`rankThresholdLogConsumableBounds_JInput`, after which the existing bridge
proves `topDown_shift_step`.

## Verdict

Ambition D achieved, with one concrete `JInput` row-strength lemma proved. The
remaining gap is the restricted-execution/recurrence-consumption simulation,
not the delayed-row residual pathology, top packing, or shift arithmetic.
