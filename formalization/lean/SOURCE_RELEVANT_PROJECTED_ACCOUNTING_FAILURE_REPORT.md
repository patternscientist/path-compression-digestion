# Source-Relevant Projected Accounting Failure Report

Branch: `lean-source-relevant-projected-accounting-v1`

Starting base:

```text
origin/main = ee3fb63f8d1ad44cb255b8c51598baf62a1fbbb4
merged prerequisite = a0421fba100f6021444f42be42f2d6ef23e5b976
```

## Summary

This worker did not prove:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

The direct rank-threshold accounting target is now proved:

```lean
E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

The proof uses the source-step case split that was missing after the
bottom-exception counterexample.  Bottom projected exceptional cost is made
source-relevant: source-rootpath-only projected artifacts are assigned zero,
while source-nonroot bottom exceptions are counted by boundary edge units and
charged to the stable rank-threshold bottom side.

## Mechanical Progress

New source-step definition:

```lean
noncomputable def RawCompressionStep.sourceRelevantBottomExceptionalCost
```

New execution-level definitions:

```lean
noncomputable def RawCompressionExecution.bottomSourceRelevantExceptionalCostSum

noncomputable def RawCompressionExecution.canonicalBottomSourceRelevantExceptionalCostSum
```

New source-step case split theorems:

```lean
theorem RawCompressionPath.ProjectedCompressionStep.consumableCost_le_cost

theorem RawCompressionPath.ProjectedCompressionStep.exceptionalCost_le_cost

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_exceptional_of_nonroot

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_zero_of_not_nonroot

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_zero_of_root

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_le_cost

theorem RawCompressionStep.cost_le_sourceRelevantProjectedParts

theorem RawCompressionStep.sourceRelevantBottomException_after_parent_top_of_index

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_if_nonroot_not_charged
```

The last theorem proves:

```lean
S.cost <=
  bottom.consumableCost
  + S.sourceRelevantBottomExceptionalCost ...
  + top.consumableCost
  + top.nonrootIndicator
```

New execution-level accounting theorems:

```lean
theorem RawCompressionExecution.stepCostSum_le_sourceRelevantProjectedParts

theorem RawCompressionExecution.bottomSourceRelevantExceptionalCostSum_le_stepCostSum

theorem RawCompressionExecution.bottomSourceRelevantExceptionalCostSum_le_cost

theorem RawCompressionExecution.cost_le_sourceRelevantProjectedExecutions

theorem RawCompressionExecution.cost_le_canonicalSourceRelevantProjectedExecutions

theorem RawCompressionExecution.canonicalBottomSourceRelevantExceptionalCostSum_le_cost
```

New rank-threshold source-relevant accounting theorem:

```lean
theorem RawCompressionExecution.rankThreshold_sourceRelevant_projected_accounting
```

This proves the direct accounting theorem up to the single displayed
source-relevant bottom exceptional term:

```lean
E.cost <=
  Cb.consumableCost
  + E.canonicalBottomSourceRelevantExceptionalCostSum ...
  + Ct.consumableCost
  + Ct.chargedCount
```

Finally, this branch adds the conditional boundary-consumption theorem:

```lean
theorem RawCompressionExecution.rankThreshold_source_cost_le_projected_consumable_add_boundary_of_relevant_bound
```

Its only extra hypothesis is:

```lean
E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
  <= ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

Under that hypothesis, Lean proves the requested shape:

```lean
E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

Additional freshness infrastructure now proved:

```lean
theorem RawRankedForest.parentIter_eq_of_root

theorem RawCompressionPath.not_root_of_compressedVertex_of_nonroot

theorem RawCompressionPath.rankNat_lt_of_lt_active_of_nonroot

theorem RawCompressionPath.node_ne_of_lt_active_of_nonroot

theorem RawCompressionStep.after_parent_top_of_parent_top

theorem RawCompressionExecution.rankThresholdDissectionFamily_parentTop_of_adjacent

theorem RawCompressionExecution.rankThresholdDissectionFamily_parentTop_of_le

theorem RawCompressionExecution.rankThresholdDissectionFamily_parentTop_of_after_lt

theorem RawCompressionExecution.rankThreshold_sourceRelevantBottomException_future_bottom_edge_ne

def RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit

theorem RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeVertex_injective

theorem RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_le_bottomFinset_card

theorem RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_slot_natCard

theorem RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum

theorem RawCompressionExecution.rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card

theorem RawCompressionExecution.rankThreshold_source_cost_le_projected_consumable_add_boundary

theorem RawCompressionExecution.rankThreshold_source_cost_le_projected_consumable_add_boundary_add_length
```

The last theorem is the main no-repeat lemma in index form: if a source-nonroot
rank-threshold bottom projection is exceptional at slot `i`, then any raw
lower endpoint `qi` of a bottom-prefix edge in that event cannot equal a raw
lower endpoint `qj` of a bottom-prefix edge in a later slot `j`.  The proof
uses the local fact that the first event rewires `qi` to a top parent, then
propagates parent-top status through the stable rank-threshold family.

The edge-unit type packages exactly the finite objects that should be counted:
a source-nonroot exceptional slot plus a lower endpoint of a bottom-prefix
edge.  Lean now proves these edge units inject into the stable bottom finset,
their cardinality is bounded by `|X_b|`, and their cardinality is exactly the
numeric source-relevant bottom exceptional sum.

## Exact Source-Step Cases

1. Source rootpath:
   - `S.path.IsRootPath S.before`.
   - `S.cost = 0`.
   - Bottom projected exceptional cost may be positive, as shown by
     `RawCompressionStep.exists_rankThreshold_bottomExceptionalCost_gt_bottomFinset_card`.
   - It is source-rootpath-only and is bypassed by
     `sourceRelevantBottomExceptionalCost = 0`.

2. Source nonrootpath with charged bottom projection:
   - The bottom projected step is nonroot-like.
   - Its bottom cost is recurrence-consumable and appears in
     `Cb.consumableCost`.
   - No bottom exceptional boundary payment is needed for that part.

3. Source nonrootpath with root-like bottom projection:
   - This is source-cost-relevant bottom exceptional cost.
   - It is now isolated by `sourceRelevantBottomExceptionalCost`.
   - It should be paid by the stable bottom boundary term `|X_b|`.

4. Top projected nonroot/cross-boundary case:
   - Paid by `Ct.chargedCount`.
   - Existing theorem `chargedCount_le_length` can consume it by `m`.

5. Top projected root-like/source-rootpath-only case:
   - Already bypassed by the earlier top-consumable theorem
     `RawCompressionStep.topProjectedStep_cost_eq_consumableCost_of_source_nonroot`
     plus the rootpath `S.cost = 0` branch.

## Resolved Boundary Blocker

The previous blocker was the boundary charging theorem for the
source-relevant bottom exceptional sum.  The finite edge-unit injection into
the stable bottom side has now been combined with the counting bridge
identifying the numeric exceptional sum with the cardinality of that edge-unit
type:

```lean
theorem rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fintype.card
        (E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s) =
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
```

Combining this with
`rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_le_bottomFinset_card`
now gives the desired boundary theorem:

This is not the false theorem:

```lean
Cb.exceptionalCost <= |X_b|
```

That statement was mechanically refuted on the previous branch.  The needed
statement is source-relevant:

```lean
theorem rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
      <= ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

The existing conditional theorem now immediately gives:

```lean
E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

## Verdict

Ambition B achieved for the source-relevant projected accounting layer.
Source-rootpath-only bottom exceptions are bypassed in Lean, future re-use of
a source-relevant bottom exceptional lower endpoint is ruled out for
rank-threshold executions, the packaged edge units inject into `|X_b|`, and
the unconditional direct source-cost accounting theorem is proved.

The remaining gap is recurrence consumption: the theorem still exposes
`Cb.consumableCost` and `Ct.consumableCost`; consuming those terms into the
`topDownCost` recurrence is separate from the source-relevant boundary
accounting completed here.
