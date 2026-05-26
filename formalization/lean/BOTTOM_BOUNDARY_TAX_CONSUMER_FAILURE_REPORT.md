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

The first pass added the checked conditional boundary-tax consumer:

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

The continuation pass added the missing recurrence consumer:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomTaxedTopDownCostBounds (k : Nat) : Prop

theorem RawCompressionExecution
  .topDown_shift_step_of_rankThresholdJInputBottomTaxedTopDownCostBounds
    (k : Nat)
    (hbottomTax :
      RankThresholdJInputBottomTaxedTopDownCostBounds k) :
    topDownShiftStepTarget k

theorem RawCompressionExecution
  .sourceRecurrence_topDownCost_of_rankThresholdJInputBottomTaxedTopDownCostBounds
    (hbottomTax : forall k : Nat,
      RankThresholdJInputBottomTaxedTopDownCostBounds k) :
    SourceRecurrence topDownCost

theorem RawCompressionExecution
  .paper_finite_bound_topDownCost_of_rankThresholdJInputBottomTaxedTopDownCostBounds
    (hbottomTax : forall k : Nat,
      RankThresholdJInputBottomTaxedTopDownCostBounds k)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    topDownCost m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

This bridge uses strong induction on the ambient rank.  It accepts a bottom
bound of the form:

```lean
Cb.consumableCost + X <= topDownCost Cb.chargedCount Bcard s + Bcard
```

It then pays the smaller-rank `topDownCost` by the induction hypothesis and
pays the extra `Bcard` in the usual diamond boundary budget.

The downstream source recurrence and paper-facing finite theorem are therefore
closed conditional on the single uniform taxed-bottom premise.

The next continuation sharpened that premise one more step:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomChargedProjectedTopDownCostBounds
    (k : Nat) : Prop

theorem RawCompressionExecution
  .rankThresholdJInputBottomTaxedTopDownCostBounds_of_chargedProjectedTopDownCostBounds
    (k : Nat)
    (hcharged :
      RankThresholdJInputBottomChargedProjectedTopDownCostBounds k) :
    RankThresholdJInputBottomTaxedTopDownCostBounds k
```

Thus the boundary tax and source-relevant exception sum are now fully consumed
by existing cost equality and bottom-card accounting.  The remaining theorem is
only about the charged projected bottom cost and ordinary `topDownCost`.

The latest continuation made the false-premise dependency explicit and added a
small ordinary-step obstruction lemma:

```lean
theorem RawCompressionStep
  .after_parent_eq_before_parent_of_cost_eq_zero
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (hcost : S.cost = 0) :
    S.after.parent = S.before.parent

theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedCost_le_topDownCost_of_skeleton_consecutive
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
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      topDownCost Cb.chargedCount Bcard s

def RawCompressionExecution
  .RankThresholdJInputBottomChargedSkeletonConsecutive (k : Nat) : Prop

theorem RawCompressionExecution
  .rankThresholdJInputBottomChargedProjectedTopDownCostBounds_of_chargedSkeletonConsecutive
    (k : Nat)
    (hstate : RankThresholdJInputBottomChargedSkeletonConsecutive k) :
    RankThresholdJInputBottomChargedProjectedTopDownCostBounds k
```

The first lemma rules out treating a state-changing boundary exception as a
zero-cost ordinary source step.  The last two declarations show precisely that
the current charged-only skeleton route would prove the sharp remaining
premise only under the known-bad consecutive-state condition.

The newest continuation discharged the trivial edge cases of that sharp
premise and named the positive core:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_cost_eq_zero_of_chargedCount_eq_zero

theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedCost_le_topDownCost_of_chargedCount_zero

theorem RawCompressionExecution
  .rankThresholdBottomProjectedExecution_bottomFinset_card_pos_of_chargedCount_pos

theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedCost_le_topDownCost_of_bottomCard_zero

def RawCompressionExecution
  .RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore
    (k : Nat) : Prop

theorem RawCompressionExecution
  .rankThresholdJInputBottomChargedProjectedTopDownCostBounds_of_positiveCore
    (k : Nat)
    (hcore :
      RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore k) :
    RankThresholdJInputBottomChargedProjectedTopDownCostBounds k
```

So the remaining theorem no longer has to consider zero charged-count or empty
bottom-card cases.  A positive charged bottom projected count now formally
implies a nonempty stable bottom side.

The pass still does not prove `RankThresholdJInputBottomConsumableBounds` or
the charged-projected `topDownCost` premise unconditionally, because the only
currently available way to prove that premise is through the charged
skeleton/topDownCost bridge, which still has the conditional
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

The first-pass non-inductive attempt would have needed the false-shape
inequality:

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

That is not derivable from `hprev` alone.  The continuation pass avoids asking
for it by proving the inductive consumer
`topDown_shift_step_of_rankThresholdJInputBottomTaxedTopDownCostBounds`.

The remaining bottom premise is now:

```lean
Cb.consumableCost + X <= topDownCost Cb.chargedCount Bcard s + Bcard
```

where `X` is the source-relevant bottom exceptional cost sum and `s` is the
rank-threshold logarithm.  The existing conditional theorem proves this only
when the charged bottom skeleton has consecutive states.

## 6. Obstruction Classification

The obstruction is theorem shape, not missing boundary-cardinality accounting
and not routine Nat arithmetic.

The boundary-card theorem is already strong enough to pay the
source-relevant boundary-exception tax.  The new theorem confirms this in the
charged-topDownCost lane.

What remains missing is a way to prove
`RankThresholdJInputBottomChargedProjectedTopDownCostBounds` without relying on
the false/wrong-object charged-only consecutive-state theorem.  Equivalently,
one needs either:

1. a projected theorem bounding the charged bottom projected cost by
   `topDownCost Cb.chargedCount Bcard s`; or
2. a repaired ordinary bottom realization whose boundary slots align the
   states, together with an erasure/accounting theorem showing that those
   boundary slots do not consume ordinary recurrence length.

## 7. Smallest Next Theorem Statement

After the zero-case reduction, the smallest theorem is the positive core:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_chargedProjectedCost_le_topDownCost_bottomCard_positiveCore
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
    (hcharged_pos : 0 < Cb.chargedCount)
    (hbottom_pos : 1 <= Bcard) :
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      topDownCost Cb.chargedCount Bcard s
```

This theorem is exactly
`RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore k`; the
checked bridge
`rankThresholdJInputBottomChargedProjectedTopDownCostBounds_of_positiveCore`
converts it to `RankThresholdJInputBottomChargedProjectedTopDownCostBounds k`.
From there, the existing bridge converts it to the taxed-bottom premise, and
the inductive consumer proves the shift step.

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

This non-inductive theorem is no longer the preferred next step; the inductive
consumer has replaced it.

## Verdict

Ambition C-style infrastructure for the recurrence consumer is now checked, and
the downstream recurrence/paper-facing theorem is closed conditional on the
uniform charged-projected `topDownCost` premise.  The unconditional bottom
field remains blocked by the missing proof of
`RankThresholdJInputBottomChargedProjectedTopDownCostBounds`; the known charged
skeleton route still depends on the false/wrong-object consecutive-state
premise.
