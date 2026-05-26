# Bottom Boundary-Tax Consumer Failure Report

Branch: `lean-bottom-boundary-tax-consumer-v1`

Starting base:

```text
2b1eb7a89f15144046ee3a937077551c5f587f7c
Sharpen bottom boundary projected obstruction
```

## Summary

This pass followed the direct projected-accounting route and did not try to
turn source-relevant boundary exceptions into ordinary rootpath/no-op
`RawCompressionStep`s.

The pass added the checked conditional boundary-tax consumer:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_taxedConsumable_le_topDownCost_add_bottomCard_of_skeleton
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hstate :
      (E.rankThresholdBottomChargedExecutionSkeleton hE s i0)
        .HasConsecutiveStates) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost + X <=
      topDownCost Cb.chargedCount Bcard s + Bcard
```

This is the exact boundary-tax shape available from the current ordinary
charged skeleton.  It consumes the charged projected bottom part through the
existing charged ordinary skeleton/topDownCost bridge, and consumes the
source-relevant boundary-exception part through the existing boundary-card
accounting.

It does not close `RankThresholdJInputBottomConsumableBounds`, because the
charged skeleton/topDownCost bridge still has the conditional
`HasConsecutiveStates` premise.  That premise is the known wrong-object
obstruction for charged-only skeletons: skipped source-relevant boundary
exceptions can change the bottom restricted parent map.

## 1. Exact Bottom Projected Cost Decomposition Theorem Used

The direct consumable split is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
```

with statement:

```lean
(E.canonicalBottomProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).consumableCost =
  (E.rankThresholdBottomChargedProjectedExecution hE s).cost
```

The boundary-inclusive projected cost package remains:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_cost_eq_consumable_add_boundary
```

and the direct charged-plus-boundary-card accounting theorem remains:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_consumable_add_boundary_le_chargedProjected_add_bottomCard
```

## 2. Exact Charged Skeleton/TopDownCost Theorem Used

The only available charged ordinary skeleton/topDownCost theorem is conditional:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomProjectedExecution_consumableCost_le_topDownCost_bottomCard_of_skeleton_consecutive
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hstate :
      (E.rankThresholdBottomChargedExecutionSkeleton hE s i0)
        .HasConsecutiveStates) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost <= topDownCost Cb.chargedCount Bcard s
```

This theorem uses the ordinary charged skeleton:

```lean
RawCompressionExecution.rankThresholdBottomChargedExecutionSkeleton
```

and its cost equality:

```lean
RawCompressionExecution
  .rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost
```

## 3. Exact Boundary-Card Theorem Used

The boundary-card accounting theorem used is:

```lean
theorem RawCompressionExecution
  .rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s) <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

## 4. Exact Boundary-Tax Term

The local boundary-tax term is:

```lean
let X :=
  E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
```

The stable bottom-card tax that pays it is:

```lean
let Bcard :=
  (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
```

The checked boundary-tax consumer proves:

```lean
Cb.consumableCost + X <= topDownCost Cb.chargedCount Bcard s + Bcard
```

under the charged skeleton consecutive-state premise.

## 5. Exact JInput Arithmetic Inequality Needed

To absorb the boundary tax into the bottom side of the shifted recurrence, the
needed inequality is:

```lean
topDownCost Cb.chargedCount Bcard s + Bcard <=
  (k + 1) * Cb.chargedCount +
    2 * Bcard * (JInput k).diamond s
```

where:

```lean
s := ceilLog2 ((JInput k).g r)
Cb :=
  E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
Bcard :=
  (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
```

The previous-row source bound only gives:

```lean
topDownCost Cb.chargedCount Bcard s <=
  k * Cb.chargedCount + 2 * Bcard * (JInput k).g s
```

That is not the required diamond-budget inequality.  The missing ingredient is
a same-row/smaller-rank recurrence consumer, not a Nat arithmetic cleanup.

## 6. Obstruction Classification

The obstruction is theorem shape, not missing boundary-cardinality accounting
and not routine Nat arithmetic.

The boundary-card theorem is already strong enough to pay the
source-relevant boundary-exception tax.  The new theorem confirms this in the
charged-topDownCost lane.

What remains missing is:

1. a way to use `topDownCost` for the charged bottom ordinary skeleton without
   the false/wrong-object charged-only consecutive-state theorem; or
2. a projected recurrence consumer that directly accepts the
   boundary-inclusive projected execution and its boundary-card tax; or
3. a same-row smaller-rank theorem proving the `topDownCost + Bcard` diamond
   absorption inequality above.

## 7. Smallest Next Theorem Statement

The smallest direct projected theorem that would close the bottom field is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_consumable_add_boundary_le_JInput_bottom_budget
    (k : Nat)
    {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost + X <=
      (k + 1) * Cb.chargedCount +
        2 * Bcard * (JInput k).diamond s
```

This theorem would imply `RankThresholdJInputBottomConsumableBounds` by dropping
the nonnegative boundary term.  It would also match the source-cost accounting
more directly than the current bottom field, because the source accounting
already contains the boundary-card tax.

The smallest topDownCost-tax theorem, if the proof stays with ordinary charged
skeleton consumption, is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_topDownCost_add_boundaryTax_le_JInput_bottom_budget
    (k : Nat)
    {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    topDownCost Cb.chargedCount Bcard s + Bcard <=
      (k + 1) * Cb.chargedCount +
        2 * Bcard * (JInput k).diamond s
```

This is not currently derivable from `hprev` alone.

## Verdict

Ambition D, with a checked conditional Ambition-C-style theorem.  The
boundary-tax consumer exists under the charged skeleton's existing
consecutive-state condition, but the unconditional bottom field remains blocked
by the charged skeleton/topDownCost theorem shape and by the missing
`topDownCost + Bcard` diamond absorption theorem.
