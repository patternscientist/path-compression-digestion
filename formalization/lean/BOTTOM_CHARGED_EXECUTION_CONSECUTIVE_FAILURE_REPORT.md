# Bottom Charged Execution Consecutive-State Failure Report

Branch: `lean-padded-top-execution-assembly-v1`

Continuation target:

```lean
RawCompressionExecution
  ((E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)
  ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
  s
```

This is the current bottom charged execution skeleton:

```lean
RawCompressionExecution.rankThresholdBottomChargedExecutionSkeleton hE s i0
```

It already has valid slots, rank-threshold packing, and exact cost:

```lean
rankThresholdBottomChargedExecutionSkeleton_hasValidSteps
rankThresholdBottomChargedExecutionSkeleton_hasRankThresholdPacking
rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost
```

The remaining missing field is:

```lean
(E.rankThresholdBottomChargedExecutionSkeleton hE s i0).HasConsecutiveStates
```

## New Lean Diagnostic

This continuation added the theorem:

```lean
theorem RawCompressionStep
    .exists_rankThreshold_bottom_not_charged_afterParent_ne_beforeParent
```

It proves that the bottom analogue of the top skip lemma is false.  There is a
valid rank-threshold-origin source step whose bottom projected step is
uncharged, but whose projected bottom after-parent map is not equal to its
before-parent map:

```lean
Not (S.bottomProjectedStep D hS cut hcut).IsCharged /\
  (S.bottomProjectedStep D hS cut hcut).afterParent !=
    (S.bottomProjectedStep D hS cut hcut).beforeParent
```

In words: a bottom prefix that ends at a top boundary is root-like in the
restricted bottom forest, so it is not charged by `consumableCost`; nevertheless
earlier bottom vertices in that prefix may be rewired by the original source
nonroot step.  Therefore uncharged bottom slots cannot be skipped the way
uncharged top slots were skipped.

## Why The Top Strategy Does Not Transfer

The top assembly relied on the local identity theorem:

```lean
RawCompressionStep.topProjectedStep_afterParent_eq_beforeParent_of_not_charged
```

That theorem lets the charged-only top execution skip every intervening
uncharged top projected slot while preserving the top restricted state.

For bottom projections, the analogous statement would be false.  The new Lean
witness shows:

```lean
Not bottom.IsCharged
```

does not imply:

```lean
bottom.afterParent = bottom.beforeParent
```

Thus the charged-only bottom skeleton cannot prove consecutive-state alignment
by copying:

```lean
rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between
rankThresholdTopChargedSlot_padded_after_eq_next_before
```

## Current Packaging Status

Positive bottom charged slots are packaged by:

```lean
rankThresholdBottomChargedSlot_positive_lifts_to_valid_step_with_path_eq
```

Zero-cost bottom charged slots are packaged as no-op steps by:

```lean
rankThresholdBottomChargedSlot_zero_cost_lifts_to_noop_step
```

All charged bottom slots are packaged by:

```lean
rankThresholdBottomChargedSlot_lifts_to_valid_step
rankThresholdBottomChargedStep
```

The fixed-cardinality skeleton is:

```lean
rankThresholdBottomChargedExecutionSkeleton
```

But this skeleton skips uncharged bottom slots.  Since some skipped uncharged
bottom slots can change the bottom restricted parent map, the skeleton is not
known to be a genuine ordinary execution.

## Accounting Status

The old bottom exceptional-cost gap is not the current blocker.  The
source-relevant bottom exceptional term is already charged to the stable bottom
side:

```lean
rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
rankThreshold_source_cost_le_projected_consumable_add_boundary
```

The top consumable field is also discharged by the padded top execution:

```lean
rankThresholdTopProjectedExecution_consumableCost_le_topDownCost_topBudget
rankThreshold_top_consumableCost_le_JInput_topBudget
```

The remaining bottom recurrence field is:

```lean
RankThresholdJInputBottomConsumableBounds
```

Equivalently, for:

```lean
let Cb :=
  E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
```

one still needs:

```lean
Cb.consumableCost <=
  (k + 1) * Cb.chargedCount +
    2 * Bcard * (JInput k).diamond s
```

## Smallest Next Theorem

The next theorem should not be a charged-only consecutive-state theorem.  The
new diagnostic blocks that route.

The smallest viable next interface appears to be a rank-inductive bottom
consumer: consume `Cb.consumableCost` by `topDownCost Cb.chargedCount Bcard s`
only under a same-target bound already available for strictly smaller rank
arguments.  In schematic form:

```lean
theorem rankThreshold_bottom_consumableCost_le_JInput_bottomBound_of_rank_induction
    (k : Nat)
    (hsmaller :
      forall {m n r' : Nat}, r' < r ->
        1 <= m -> 1 <= n ->
          topDownCost m n r' <=
            (k + 1) * m + 2 * n * (JInput k).diamond r')
    ... :
    Cb.consumableCost <=
      (k + 1) * Cb.chargedCount +
        2 * Bcard * (JInput k).diamond s
```

That would require strengthening the current `SourceShiftStep` packaging to
expose the standard rank-descent induction used by the top-down recurrence.
Without such a rank-inductive target-bound hypothesis, the current API only
provides the previous row bound:

```lean
SourceBound topDownCost k (JInput k).g
```

which is not the bottom field needed for the successor row.

## Verdict

Ambition C/D diagnostic progress.  The charged bottom slots are packaged and
costed, but the charged-only bottom execution cannot be completed by skipping
uncharged bottom slots.  The next repair should change the bottom consumption
interface to a rank-inductive recurrence consumer, rather than trying to prove
a false bottom skip identity.
