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

It also did not prove the unconditional direct rank-threshold accounting
target:

```lean
E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

However, it proves the source-step case split that was missing after the
bottom-exception counterexample.  Bottom projected exceptional cost is now
made source-relevant: source-rootpath-only projected artifacts are assigned
zero, while source-nonroot bottom exceptions remain explicit.

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
theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_exceptional_of_nonroot

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_zero_of_not_nonroot

theorem RawCompressionStep.sourceRelevantBottomExceptionalCost_eq_zero_of_root

theorem RawCompressionStep.cost_le_sourceRelevantProjectedParts
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

theorem RawCompressionExecution.cost_le_sourceRelevantProjectedExecutions

theorem RawCompressionExecution.cost_le_canonicalSourceRelevantProjectedExecutions
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

## Blocker

The first remaining blocker is the boundary charging theorem for the
source-relevant bottom exceptional sum.  The current API still lacks the
freshness/no-repeat argument showing that source-nonroot root-like bottom
projection events can be charged injectively to the stable bottom side.

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

Once this theorem is proved, the existing conditional theorem immediately
gives:

```lean
E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

## Verdict

Ambition C achieved, and Ambition B reduced to one explicit boundary-charging
theorem.  Source-rootpath-only bottom exceptions are bypassed in Lean.  The
unconditional direct source-cost accounting theorem is not yet proved because
the source-relevant bottom exception sum is not yet bounded by `|X_b|`.
