# Source Shift Recurrence Consumption Failure Report

Branch: `lean-source-shift-recurrence-consumption-v1`

Starting base after fetch and merge:

```text
origin/main = a7bd5751f58745ad4311071ce9e37af9b81c22d8
merged projected-accounting commit = 6016b8183327b6a7cb4af647473dcb47f4445749
```

## Summary

This worker did not prove:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

The projected source accounting theorem is now connected to the stable
rank-threshold boundary budget, but the projected executions still cannot be
consumed by `topDownCost`.  The first remaining obstruction is not
boundary-card accounting.  It is the bridge from dependent projected
executions to the concrete extremal source-cost family.

## Progress Made

The branch adds Lean wrappers in `SourceProjection.lean` proving:

```lean
theorem RawCompressionExecution.bottomBoundaryCard_le_of_forall_bottom_card_le

theorem RawCompressionExecution.bottomBoundaryCard_eq_of_forall_bottomFinset_eq

theorem RawCompressionExecution.rankThresholdDissectionFamily_rankNat_eq_of_slot

theorem RawCompressionExecution.rankThresholdDissectionFamily_bottomFinset_eq_of_slot

theorem RawCompressionExecution.rankThresholdDissectionFamily_topFinset_eq_of_slot

theorem RawCompressionExecution.rankThreshold_bottomBoundaryCard_le_bottomFinset_card

theorem RawCompressionExecution.rankThreshold_bottomBoundaryCard_eq_bottomFinset_card

theorem RawCompressionExecution.rankThresholdDissectionFamily_bottom_rank_le

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_shifted_rank_le

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_card_le_div

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_card_le_div_of_slot_packing

theorem RawCompressionExecution.rankThreshold_projected_nonroot_count_le

theorem RawCompressionExecution.rankThreshold_projected_cost_main_lemma
```

It also adds the reusable extremal-cost handles in
`ConcreteSourceModel.lean`:

```lean
theorem RawCompressionExecution.cost_le_topDownCost

theorem topDownCost_le_of_forall_valid
```

The projected execution API now includes:

```lean
theorem ProjectedCompressionExecution.nonrootCount_le_length

theorem ProjectedCompressionExecution.chargedCount_le_length
```

These provide the projected form of the `|C_t| <= m` recurrence handle.

The existing base-budget proof now uses `topDownCost_le_of_forall_valid`,
making explicit the standard route for consuming per-execution bounds into
the finite supremum defining `topDownCost`.

The key bridge is:

```lean
theorem RawCompressionExecution.rankThreshold_bottomBoundaryCard_eq_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.bottomBoundaryCard (E.rankThresholdDissectionFamily hE.1 s) =
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

For nonempty executions, this relates the supremum-shaped
`bottomBoundaryCard` to the stable rank-threshold bottom side at any chosen
slot.  This is the intended `|X_b|` bridge in equality form.

The rank-threshold side bounds are now exposed at the execution-family level:

```lean
theorem RawCompressionExecution.rankThresholdDissectionFamily_bottom_rank_le :
    RawRankedForest.rankNat (E.step i).before v.1 <= s

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_shifted_rank_le :
    RankThresholdDissection.topShiftedRank (E.step i).before (hsteps i).1.1 s v <=
      r - s - 1

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_card_le_div :
    (E.rankThresholdDissectionFamily hsteps s i).topFinset.card <=
      n / 2 ^ (s + 1)

theorem RawCompressionExecution.rankThresholdDissectionFamily_top_card_le_div_of_slot_packing :
    (E.rankThresholdDissectionFamily hsteps s i).topFinset.card <=
      n / 2 ^ (s + 1)
```

The top cardinality theorem remains conditional on the existing
`RankThresholdDissection.TopPacking` witness, but the bound can now be
transported from a packing witness at any chosen slot across the stable
rank-threshold family.  The current concrete forest model still does not
derive that packing witness from child/subtree semantics.

The projected main lemma is also specialized to rank-threshold families:

```lean
theorem RawCompressionExecution.rankThreshold_projected_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      Cb.projectedCost + Ct.projectedCost +
        ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
          Ct.chargedCount
```

where `Cb` and `Ct` are the canonical rank-threshold bottom/top projected
executions.  This consumes the projected accounting theorem up to the exact
stable `|X_b|` bridge.

## First Failed Bridge

The first failed bridge is:

```text
projected accounting -> topDownCost recurrence consumption
```

The accounting theorem has the shape:

```lean
E.cost <=
  Cb.projectedCost + Ct.projectedCost +
    E.bottomBoundaryCard D + Ct.chargedCount
```

where `Cb` and `Ct` are dependent
`RawCompressionPath.ProjectedCompressionExecution`s.  But the recurrence
premise in `topDownShiftStepTarget` bounds only:

```lean
topDownCost m n r
```

and `topDownCost` is a finite supremum over ordinary
`RawCompressionExecution m n r` objects satisfying `RawCompressionExecution.IsValid`,
including `HasBaseRankAccounting`.

There is currently no theorem converting, simulating, or bounding:

```lean
ProjectedCompressionExecution.projectedCost
```

by an appropriate `topDownCost` value.  The new
`RawCompressionExecution.cost_le_topDownCost` and
`topDownCost_le_of_forall_valid` lemmas expose the extremal-cost API needed
after such a materialized valid execution exists; they do not themselves
materialize projected executions.

## Blocker Classification

1. Boundary-card accounting: not the first blocker.  The new
   `rankThreshold_bottomBoundaryCard_eq_bottomFinset_card` theorem shows that
   `bottomBoundaryCard` is exactly the stable bottom-side cardinality for
   nonempty rank-threshold executions.
2. Rank bounds: bottom and shifted-top rank bounds are proved at the
   rank-threshold family level.
3. Cardinality arithmetic: the divided top-cardinality bound is available only
   from a `TopPacking` witness; deriving that witness remains open.
4. Extremal `topDownCost` consumption: primary blocker.  Projected executions
   are not ordinary valid, base-accounted `RawCompressionExecution`s.

## Exact Next Theorem Needed

The next theorem should not be the full shift step.  The next theorem should be
a cost-consumption bridge for rank-threshold projected executions, for example
an inequality-form materialization theorem of this kind:

```lean
theorem rankThresholdBottomProjectedExecution_projectedCost_le_topDownCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).projectedCost <=
      topDownCost m
        ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
        s
```

and a corresponding top-side theorem, with the top-side rank
`r - s - 1`, the top-side cardinality bound, and the correct top execution
length/count parameter.  Proving either theorem will likely require a
restricted-projection simulation API, because projected steps do not currently
match `RawCompressionStep.IsValid`.

## Shape of `bottomBoundaryCard`

`bottomBoundaryCard` is well-shaped for the intended stable dissection use:
it is a supremum over step-indexed bottom sides, and for nonempty
rank-threshold families the bottom side is stable across all slots, so the
supremum equals any chosen bottom side.  For arbitrary families, the supremum
is stronger than a single displayed side and remains appropriate as a safe
finite budget.

The definition is not the recurrence blocker.  The blocker is that the cost
terms adjacent to it are still projected costs, not costs of valid restricted
source executions accepted by `topDownCost`.

## Does `topDownShiftStepTarget` Match the Projected Lemma?

Not directly.

`topDownShiftStepTarget` is the right paper-facing target:

```lean
SourceBound topDownCost k (JInput k).g ->
  SourceBound topDownCost (k + 1) (JInput k).diamond
```

But the current projected accounting theorem proves only an internal
execution-level inequality for `ProjectedCompressionExecution`s.  A
materialization/simulation theorem is required before the projected lemma can
be consumed by the existing `SourceBound topDownCost ...` premise.

## Remaining Gap

The remaining gap is to prove that rank-threshold bottom/top projected
executions can be simulated by, or bounded by, ordinary source executions in
the `topDownCost` family, including the necessary validity and base-accounting
data or a justified refactor of the cost-family API.  After that bridge is
available, the arithmetic recurrence step can be attempted.

## Verdict

Ambition C achieved in Lean, with partial Ambition B wrappers strengthened to
slot-stable equality/cardinality transport.  Ambition A is not achieved.
