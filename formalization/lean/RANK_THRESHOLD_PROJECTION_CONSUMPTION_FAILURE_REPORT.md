# Rank-Threshold Projection Consumption Failure Report

Branch: `lean-rank-threshold-projection-consumption-v1`

Starting base:

```text
origin/main = da6d13230e41bab3695281c0b57ebfc948bcb296
merged prerequisite = 1bfa82cc3ee728ab93dee002d4c708bb58b913b7
```

## Summary

This worker did not prove:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

It also did not prove a rank-threshold projected-cost domination theorem by
`topDownCost`.  The previous counterexamples remain valid, and no blanket
`ProjectedCompressionExecution.IsAdmissible -> projectedCost <= topDownCost`
statement was added.

The successful Lean progress is a narrower consumption split.  Projected cost
is now split into recurrence-consumable nonroot-like cost and exceptional
root-like cost.  For projected top sides that arise from actual valid source
steps, the exceptional top cost is not needed in the source-cost accounting:
on source nonrootpaths the top projection is consumable, and on source
rootpaths the source cost is zero.

## Mechanical Progress

New projected-step definitions:

```lean
noncomputable def RawCompressionPath.ProjectedCompressionStep.consumableCost

noncomputable def RawCompressionPath.ProjectedCompressionStep.exceptionalCost
```

New projected-execution definitions:

```lean
noncomputable def RawCompressionPath.ProjectedCompressionExecution.consumableCost

noncomputable def RawCompressionPath.ProjectedCompressionExecution.exceptionalCost
```

New split theorems:

```lean
theorem RawCompressionPath.ProjectedCompressionStep.cost_eq_consumableCost_add_exceptionalCost

theorem RawCompressionPath.ProjectedCompressionExecution.projectedCost_eq_consumableCost_add_exceptionalCost
```

New top-exception removal theorems:

```lean
theorem RawCompressionStep.topProjectedStep_cost_eq_consumableCost_of_source_nonroot

theorem RawCompressionStep.cost_le_bottomCost_add_topConsumable_add_topNonroot

theorem RawCompressionExecution.stepCostSum_le_bottomProjectedCostSum_add_topConsumableCost_add_topProjectedNonrootCount

theorem RawCompressionExecution.cost_le_projectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount

theorem RawCompressionExecution.cost_le_canonicalProjectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount
```

New rank-threshold specialization:

```lean
theorem RawCompressionExecution.rankThreshold_projected_consumable_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      Cb.projectedCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

where `Cb` and `Ct` abbreviate the canonical rank-threshold bottom and top
projected executions, and `|X_b|` is the stable bottom finset cardinality.

The length-consumed form is also proved:

```lean
theorem RawCompressionExecution.rankThreshold_projected_consumable_cost_main_lemma_add_length
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      Cb.projectedCost + Ct.consumableCost + |X_b| + m
```

Continuing from this split, Lean also proves that the naive theorem
`bottom exceptionalCost <= |X_b|` is false as stated, even for a valid
rank-threshold-origin projected step:

```lean
theorem RawCompressionStep.exists_rankThreshold_bottomExceptionalCost_gt_bottomFinset_card :
    Exists fun S : RawCompressionStep 2 1 =>
      Exists fun hS : S.IsValid =>
        let D := RankThresholdDissection.dissection S.before hS.1.1 0
        Exists fun cut : Nat =>
          Exists fun hcut : S.path.HasDissectionCut D cut =>
            D.bottomFinset.card <
              (S.bottomProjectedStep D hS cut hcut).exceptionalCost
```

The witness is a source rootpath.  Its source cost is zero, but its bottom
projection can still have positive root-like projected edge cost.  Therefore
the next bottom theorem must either ignore source-rootpath bottom exceptional
costs or prove a direct source-cost accounting bound rather than a blanket
bound on `Cb.exceptionalCost`.

## Exact Theorem Now Almost Proved

The theorem needed before recurrence arithmetic is:

```lean
theorem rankThreshold_projected_consumable_cost_bound
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

or the length-consumed version with `+ m`.

The current Lean theorem proves the same statement except that the bottom term
is still:

```lean
Cb.projectedCost
```

instead of:

```lean
Cb.consumableCost
```

Equivalently, the remaining missing bridge is the rank-threshold-origin
bottom exceptional-cost payment.

## Exceptional Cases

Top exceptional projected cost:

- Case: the original source path is a rootpath.
- Case: the top suffix is empty.
- Case: the top suffix is nonempty but root-like.

For source-origin top projections, these cases are now handled in Lean.  The
exceptional top cost is not paid by a new additive term; it is removed from the
source-cost inequality.  The existing `Ct.chargedCount` term still pays the
one cross-dissection charge when the top projected path is nonroot-like, and
`chargedCount_le_length` consumes it by `m`.

Bottom exceptional projected cost:

- Case: the bottom projection is root-like because the cut boundary has a
  nonempty top suffix.
- Case: the whole active path is bottom, but the target is a restricted
  bottom root because its original parent lies in the top side.
- Case: source rootpaths can also create root-like bottom projected edge cost,
  although their original source cost is zero and should not need payment.

These bottom cases are not yet consumed by `topDownCost`.  The intended payer
is the existing stable bottom-side term `|X_b|`, represented in Lean by
`rankThreshold_bottomBoundaryCard_eq_bottomFinset_card`.  However, the current
API has not yet proved the freshness/no-repeat/compression argument needed to
charge the necessary bottom root-like projected work injectively to `X_b`.
Moreover, the new theorem
`RawCompressionStep.exists_rankThreshold_bottomExceptionalCost_gt_bottomFinset_card`
shows that such a theorem cannot bound all bottom exceptional projected cost:
source-rootpath bottom exceptional cost must be excluded or bypassed because
it never contributes to the original source cost.

## Existing Additive Terms

- `Ct.chargedCount`: pays the top projected nonroot/cross-edge charge; already
  bounded by `m`.
- `bottomBoundaryCard`, specialized by
  `rankThreshold_bottomBoundaryCard_eq_bottomFinset_card`: intended to pay the
  bottom boundary/root-like exceptional work, but the injection/charging
  theorem is still missing.
- `m`: available through
  `rankThreshold_projected_consumable_cost_main_lemma_add_length`.

## Are New Definitions Needed?

Yes.  Existing `IsRootLike`, `IsCharged`, `boundaryCharge`, and `chargedCount`
identify charged top nonroot work, but they did not expose the cost split.
The new `consumableCost` and `exceptionalCost` definitions are the minimal
cost-level split needed to state the remaining theorem without invalidating
the one-vertex counterexamples.

`boundaryCharge` is currently the projected nonroot indicator.  It is useful
for the top charged term, but it is not itself a measure of root-like
exceptional bottom cost.

## Smallest Next Theorem

The smallest next theorem is not the blanket bottom exceptional payment theorem:
the following statement is now mechanically refuted when interpreted over all
bottom exceptional projected cost:

```lean
theorem rankThreshold_bottomExceptionalCost_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).exceptionalCost <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

The exact theorem should instead ignore source-rootpath-only projected bottom
cost, either by defining a source-relevant bottom exceptional cost, or by
proving the direct accounting statement:

```lean
theorem rankThreshold_projected_consumable_cost_bound :
    E.cost <= Cb.consumableCost + Ct.consumableCost + |X_b| + Ct.chargedCount
```

After that, the remaining bridge is to prove that `Cb.consumableCost` and
`Ct.consumableCost` are bounded by the appropriate recurrence/topDownCost
terms for rank-threshold-origin projections.

## Verdict

Ambition D with Lean progress toward Ambition C.  Projected cost is split, and
top exceptional projected cost is removed from rank-threshold accounting.  The
remaining blocker is bottom exceptional projected cost and the subsequent
rank-threshold-specific `topDownCost` consumption of consumable projected
costs.
