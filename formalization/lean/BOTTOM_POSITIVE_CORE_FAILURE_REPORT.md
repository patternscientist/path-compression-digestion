# Bottom Positive-Core Failure Report

Branch: `lean-bottom-positive-core-v1`

Starting base:

```text
d9b0dfe88c805420105a511c55ac8ad8a54b820f
bottom boundary tax consumer reduction
```

## Summary

This pass did not use
`RawCompressionExecution.RankThresholdJInputBottomChargedSkeletonConsecutive`.
That is the known wrong route: the charged-only ordinary skeleton can skip
state-changing source-relevant bottom boundary exceptions, so its consecutive
state premise is not the right theorem to prove.

The positive-core target remains open.  The checked progress is a local
obstruction theorem showing that projected admissibility, even with a positive
charged projected slot, is not enough to feed the ordinary `topDownCost`
interface:

```lean
theorem RawCompressionPath.ProjectedCompressionExecution
  .exists_admissible_chargedProjectedCost_gt_topDownCost_rank_zero :
    Exists fun E : ProjectedCompressionExecution 1 =>
      E.IsAdmissible /\ E.chargedCount = 1 /\ E.projectedCost = 1 /\
        topDownCost 1 2 0 = 0
```

So a projected-extremal consumer cannot be stated from
`ProjectedCompressionExecution.IsAdmissible` and positive charged count alone.
It must use the special rank-threshold origin of
`rankThresholdBottomChargedProjectedExecution`, or else construct a genuine
ordinary valid execution with at least the same cost.

This continuation also proves the elementary local range estimate:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_cost_le_threshold_mul_chargedCount
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      s *
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount
```

This confirms that each charged bottom projected slot is locally range-bounded.
It still does not prove the positive core: the target needs domination by
`topDownCost Cb.chargedCount Bcard s`, not by the crude coefficient `s` times
the charged count.  Thus the gap is not a missing per-slot length bound; it is
the missing structural recurrence/realization theorem.

## 1. Expanded Positive-Core Target

The exact expanded target is:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (_hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    0 < Cb.chargedCount ->
      1 <= Bcard ->
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
          topDownCost Cb.chargedCount Bcard s
```

The hypotheses `0 < Cb.chargedCount` and `1 <= Bcard` are exactly the
nondegenerate cases left after the previous zero-case reduction.

## 2. Exact Charged Bottom Projected Object

The object to consume is:

```lean
E.rankThresholdBottomChargedProjectedExecution hE s
```

with definition:

```lean
noncomputable def RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    RawCompressionPath.ProjectedCompressionExecution
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)
```

Its cost is already identified with the full bottom projected consumable cost:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_cost_eq_consumableCost
```

and equivalently:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
```

## 3. Why The Old Charged-Only Consecutive Premise Is Not Used

The theorem

```lean
RawCompressionExecution.RankThresholdJInputBottomChargedSkeletonConsecutive
```

would imply the sharp charged-projected `topDownCost` premise through:

```lean
theorem RawCompressionExecution
  .rankThresholdJInputBottomChargedProjectedTopDownCostBounds_of_chargedSkeletonConsecutive
```

but this is only a diagnostic bridge.  It is not used here because the premise
is known to be the wrong object: skipped uncharged source-relevant boundary
exceptions can change the bottom restricted parent map.

## 4. Can The Charged Projected Object Use Existing `topDownCost` API?

Not directly.

The existing ordinary consumer is:

```lean
theorem RawCompressionExecution.cost_le_topDownCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid) :
    E.cost <= topDownCost m n r
```

It requires a genuine ordinary `RawCompressionExecution` with valid steps,
literal consecutive states, and base/rank accounting.

The charged projected object is instead a
`RawCompressionPath.ProjectedCompressionExecution`.  Its admissibility notion
only records projected parent-map commutation up to equivalence, and the new
checked theorem

```lean
RawCompressionPath.ProjectedCompressionExecution
  .exists_admissible_chargedProjectedCost_gt_topDownCost_rank_zero
```

shows that projected admissibility plus positive charged cost is too weak to
imply any ordinary `topDownCost` domination theorem.

The newly checked local range theorem gives only:

```lean
(E.rankThresholdBottomChargedProjectedExecution hE s).cost
  <= s * Cb.chargedCount
```

This is arithmetically the wrong shape for the recurrence consumer.  Replacing
`topDownCost Cb.chargedCount Bcard s` by `s * Cb.chargedCount` would lose the
recursive row coefficient and does not fit the downstream `JInput` algebra.

## 5. Exact Projected-Extremal Theorem Needed

The smallest direct theorem is exactly the positive core, locally stated as:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedCost_le_topDownCost_positiveCore
    (k : Nat)
    {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (_hprev : SourceBound topDownCost k (JInput k).g)
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
    0 < Cb.chargedCount ->
      1 <= Bcard ->
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
          topDownCost Cb.chargedCount Bcard s
```

A more structural version that would immediately imply it is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_exists_valid_cost_ge
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Exists fun Ebot : RawCompressionExecution Cb.chargedCount Bcard s =>
      Ebot.IsValid /\
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost <= Ebot.cost
```

Then `Ebot.cost_le_topDownCost` proves the desired positive-core inequality.
This theorem must not be the old charged-only skeleton consecutive theorem; it
may build a different ordinary execution or prove an equivalent lower-bound
principle for `topDownCost`.

## 6. Missing Rank/Base/Cardinality/Accounting Theorem

The obstruction is not the zero charged-count case, not the zero bottom-card
case, and not boundary-card accounting:

```lean
rankThresholdBottomChargedProjectedExecution_cost_eq_zero_of_chargedCount_eq_zero
rankThresholdBottomChargedProjectedCost_le_topDownCost_of_chargedCount_zero
rankThresholdBottomProjectedExecution_bottomFinset_card_pos_of_chargedCount_pos
rankThresholdBottomChargedProjectedCost_le_topDownCost_of_bottomCard_zero
rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
```

are already available.

The missing theorem is an ordinary-realization or lower-bound theorem for the
rank-threshold-origin charged projected cost.  It must be stronger than the
local range estimate above.  The existing per-slot lift:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedSlot_lifts_to_valid_step
```

proves that each charged slot has a valid ordinary bottom step with matching
cost and endpoint packing.  What is missing is the global packaging theorem
that turns those per-slot realizations into a single valid ordinary execution
of length `Cb.chargedCount` over `Bcard` vertices, or otherwise proves that
`topDownCost Cb.chargedCount Bcard s` is at least their total cost.

## 7. Smallest Next Theorem Statement

The smallest useful next theorem is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_exists_valid_cost_ge
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard :=
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Exists fun Ebot : RawCompressionExecution Cb.chargedCount Bcard s =>
      Ebot.IsValid /\
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost <= Ebot.cost
```

A proof of this statement should use the rank-threshold origin of the charged
projected slots and the existing per-slot lift theorem.  It should not assert
that `rankThresholdBottomChargedExecutionSkeleton` has consecutive states.

## Verdict

Ambition D achieved.  The positive core is not closed.  The exact blocker is
the absence of an ordinary `topDownCost` lower-bound/realization theorem for
the rank-threshold charged projected execution.  A generic projected-admissible
consumer is formally ruled out by a checked positive charged counterexample.
