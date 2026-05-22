# Source Shift Failure Report

Branch: `lean-source-shift-main-lemma-v1`

Starting commit: `4d6febfe0ea9cd10cc99d73d029e3491f5b63a8a`

## Summary

This branch adds the first source-dissection and source-projection Lean
modules:

```text
PathCompressionDigestion/SourceDissection.lean
PathCompressionDigestion/SourceProjection.lean
```

The module formalizes concrete dissection structure around the existing
`ConcreteSourceModel` API, including bottom/top membership, restricted
bottom/top parent maps, local path-contiguity across a dissection, raw
nonrootpath counting, and rank-threshold dissection facts.
`SourceProjection.lean` then aggregates the one-step projected cost bounds
over raw executions and proves the source nonrootpath indicator summation.

It does not prove the Seidel--Sharir shift theorem:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

It also does not claim an unconditional `SourceRecurrence topDownCost` or an
unconditional paper-facing finite theorem.

## Objects Successfully Defined

In `PathCompressionDigestion/SourceDissection.lean`:

- `ConcreteSourceModel.DissectionSide`
- `ConcreteSourceModel.RawDissection`
- `RawDissection.IsTop`
- `RawDissection.IsBottom`
- `RawDissection.sidePred`
- `RawDissection.topFinset`
- `RawDissection.bottomFinset`
- `RawDissection.TopNode`
- `RawDissection.BottomNode`
- `RawDissection.topParent`
- `RawDissection.bottomParent`
- `RawDissection.topRankNat`
- `RawDissection.bottomRankNat`
- `RawCompressionPath.ProjectedPathSegment`
- `ProjectedPathSegment.edgeCost`
- `RawCompressionPath.ProjectedCompressionStep`
- `ProjectedCompressionStep.cost`
- `RawCompressionPath.activeFinset`
- `RawCompressionPath.properFinset`
- `RawCompressionPath.projectedActiveFinset`
- `RawCompressionPath.projectedProperFinset`
- `RawCompressionPath.HasDissectionCut`
- `RawCompressionPath.bottomProjectionLength`
- `RawCompressionPath.topProjectionLength`
- `RawCompressionPath.bottomProjectionIndex`
- `RawCompressionPath.topProjectionIndex`
- `RawCompressionPath.bottomProjectionNode`
- `RawCompressionPath.topProjectionNode`
- `RawCompressionPath.bottomProjectionSegment`
- `RawCompressionPath.topProjectionSegment`
- `RawCompressionStep.afterDissection`
- `RawCompressionStep.afterTopParent`
- `RawCompressionStep.afterBottomParent`
- `RawCompressionStep.bottomProjectedStep`
- `RawCompressionStep.topProjectedStep`
- `RawCompressionExecution.stepCostSum`
- `RawCompressionExecution.nonrootCount`
- `RankThresholdDissection.topPred`
- `RankThresholdDissection.dissection`
- `RankThresholdDissection.topShiftedRank`
- `RankThresholdDissection.TopPacking`

In `PathCompressionDigestion/SourceProjection.lean`:

- `RawCompressionStep.nonrootIndicator`
- `RawCompressionPath.ProjectedPathSegment.lastIndex`
- `RawCompressionPath.ProjectedPathSegment.IsRootPath`
- `RawCompressionPath.ProjectedPathSegment.IsNonrootPath`
- `RawCompressionPath.ProjectedPathSegment.nonrootIndicator`
- `RawCompressionPath.ProjectedCompressionStep.IsNonrootPath`
- `RawCompressionPath.ProjectedCompressionStep.nonrootIndicator`
- `RawCompressionExecution.dissectionCut`
- `RawCompressionExecution.bottomProjectedCostSum`
- `RawCompressionExecution.topProjectedCostSum`
- `RawCompressionExecution.bottomProjectedNonrootCount`
- `RawCompressionExecution.topProjectedNonrootCount`

## Theorems Proved

The module proves the structural facts needed before the main source-shift
lemma can be attacked:

- `RawDissection.mem_topFinset`
- `RawDissection.mem_bottomFinset`
- `RawDissection.bottom_or_top`
- `RawDissection.not_bottom_and_top`
- `RawDissection.top_of_ancestor`
- `RawDissection.parent_top`
- `RawDissection.bottom_of_parent_bottom`
- `RawDissection.topParent_val`
- `RawDissection.bottomParent_val_of_parent_bottom`
- `RawDissection.bottomParent_val_of_parent_top`
- `ProjectedPathSegment.edgeCost_le_len`
- `RawRankedForest.rankNat_le_parent`
- `RawRankedForest.rankNat_le_parentIter`
- `RawRankedForest.parentIter_succ_eq_parent_parentIter`
- `RawRankedForest.isAncestor_parent`
- `RawRankedForest.isAncestor_of_parent_eq`
- `RawCompressionPath.mem_activeFinset`
- `RawCompressionPath.mem_properFinset`
- `RawCompressionPath.projectedActive_card_bottom_add_top`
- `RawCompressionPath.projectedProper_card_bottom_add_top`
- `RawCompressionPath.top_of_adjacent`
- `RawCompressionPath.bottom_of_adjacent`
- `RawCompressionPath.ancestor_of_le_active`
- `RawCompressionPath.top_suffix_of_le`
- `RawCompressionPath.bottom_prefix_of_le`
- `RawCompressionPath.exists_dissection_cut`
- `RawCompressionPath.bottomProjectionLength_le_len`
- `RawCompressionPath.topProjectionLength_le_len`
- `RawCompressionPath.projectionLength_add`
- `RawCompressionPath.bottomProjectionIndex_val`
- `RawCompressionPath.topProjectionIndex_val`
- `RawCompressionPath.bottomProjectionIndex_lt_cut`
- `RawCompressionPath.topProjectionIndex_ge_cut`
- `RawCompressionPath.bottomProjectionIndex_active`
- `RawCompressionPath.topProjectionIndex_active`
- `RawCompressionPath.bottomProjectionNode_val`
- `RawCompressionPath.topProjectionNode_val`
- `RawCompressionPath.bottomProjection_parent_chain`
- `RawCompressionPath.topProjection_parent_chain`
- `RawCompressionPath.bottomProjectionSegment_len`
- `RawCompressionPath.topProjectionSegment_len`
- `RawCompressionPath.cost_le_projection_edgeCosts_add_one`
- `RawCompressionPath.sourceCost_le_projection_edgeCosts_add_one`
- `RawCompressionStep.after_parent_top`
- `RawCompressionStep.afterDissection_isTop`
- `RawCompressionStep.afterDissection_isBottom`
- `RawCompressionStep.afterDissection_topFinset`
- `RawCompressionStep.afterDissection_bottomFinset`
- `RawCompressionStep.afterDissection_top_card`
- `RawCompressionStep.afterDissection_bottom_card`
- `RawCompressionStep.afterTopParent_val`
- `RawCompressionStep.afterBottomParent_val_of_parent_bottom`
- `RawCompressionStep.afterBottomParent_val_of_parent_top`
- `RawCompressionStep.exists_path_dissection_cut`
- `RawCompressionStep.exists_projection_segments_cost_bound`
- `RawCompressionStep.bottomProjectedStep_cost`
- `RawCompressionStep.topProjectedStep_cost`
- `RawCompressionStep.cost_le_projectedSteps_cost_add_one`
- `RawCompressionExecution.nonrootCount_le_length`
- `RankThresholdDissection.dissection_isTop`
- `RankThresholdDissection.dissection_isBottom`
- `RankThresholdDissection.bottom_rank_le`
- `RankThresholdDissection.rankNat_le_bound`
- `RankThresholdDissection.top_shifted_rank_le`
- `RankThresholdDissection.top_card_mul_pow_le`
- `RankThresholdDissection.top_card_le_div`
- `RawCompressionStep.cost_le_projectedSteps_cost_add_nonrootIndicator`
- `RawCompressionPath.ProjectedPathSegment.not_nonroot_iff_root`
- `RawCompressionPath.ProjectedPathSegment.nonrootIndicator_le_one`
- `RawCompressionPath.ProjectedPathSegment.nonrootIndicator_eq_zero_of_root`
- `RawCompressionPath.ProjectedPathSegment.nonrootIndicator_eq_zero_of_len_eq_zero`
- `RawCompressionPath.ProjectedPathSegment.nonrootIndicator_eq_one_of_nonroot`
- `RawCompressionPath.ProjectedCompressionStep.nonrootIndicator_le_one`
- `RawCompressionPath.bottomProjectionSegment_isRootPath_of_top_nonempty`
- `RawCompressionPath.bottomProjectionSegment_nonrootIndicator_eq_zero_of_top_nonempty`
- `RawCompressionPath.topProjectionSegment_isRootPath_of_source_root`
- `RawCompressionPath.bottomProjectionSegment_isRootPath_of_source_root_all_bottom`
- `RawCompressionPath.topProjectionSegment_isNonrootPath_of_source_nonroot`
- `RawCompressionPath.sourceCost_le_projection_edgeCosts_add_topNonrootIndicator`
- `RawCompressionStep.projected_nonrootIndicators_add_le_nonrootIndicator`
- `RawCompressionStep.cost_le_projectedSteps_cost_add_topNonrootIndicator`
- `RawCompressionExecution.cost_eq_stepCostSum`
- `RawCompressionExecution.dissectionCut_spec`
- `RawCompressionExecution.nonrootIndicator_sum_eq_nonrootCount`
- `RawCompressionExecution.projectedNonrootCounts_add_le_nonrootCount`
- `RawCompressionExecution.canonicalProjectedNonrootCounts_add_le_nonrootCount`
- `RawCompressionExecution.stepCostSum_le_projectedCostSums_add_topProjectedNonrootCount`
- `RawCompressionExecution.stepCostSum_le_canonicalProjectedCostSums_add_topProjectedNonrootCount`
- `RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_topProjectedNonrootCount`
- `RawCompressionExecution.stepCostSum_le_projectedCostSums_add_nonrootCount`
- `RawCompressionExecution.stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount`
- `RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_nonrootCount`

## Exact First Failed Theorem

The global path-contiguity theorem is now closed in the reusable cut form:

```lean
theorem RawCompressionPath.exists_dissection_cut
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F) :
    Exists (P.HasDissectionCut D)
```

The bottom/top projected path-segment objects over restricted forests are now
constructed, with parent-chain proofs:

```lean
def RawCompressionPath.bottomProjectionSegment
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    ProjectedPathSegment D.BottomNode D.bottomParent

def RawCompressionPath.topProjectionSegment
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    ProjectedPathSegment D.TopNode D.topParent
```

The first theorem not yet closed is now the step-level projection theorem:
given a valid raw compression step and a dissection cut for its path, construct
bottom/top projected compression steps over the restricted forests and prove
the restricted before/after parent maps commute with the raw step.

This branch now proves the prerequisite one-step dissection preservation:

```lean
def RawCompressionStep.afterDissection
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    RawDissection S.after

theorem RawCompressionStep.after_parent_top
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    {v : Fin n}
    (hv : D.IsTop v) :
    D.IsTop (S.after.parent v)

theorem RawCompressionStep.exists_projection_segments_cost_bound
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    Exists fun cut : Nat =>
      Exists fun hcut : S.path.HasDissectionCut D cut =>
        S.cost <=
          (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost +
            (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost + 1
```

It also packages actual projected one-step objects and aggregates their costs
over raw executions:

```lean
structure RawCompressionPath.ProjectedCompressionStep (alpha : Type*) where
  beforeParent : alpha -> alpha
  afterParent : alpha -> alpha
  path : ProjectedPathSegment alpha beforeParent

def RawCompressionStep.bottomProjectedStep ...
def RawCompressionStep.topProjectedStep ...

theorem RawCompressionStep.cost_le_projectedSteps_cost_add_one
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).cost + 1

theorem RawCompressionStep.cost_le_projectedSteps_cost_add_nonrootIndicator
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).cost + S.nonrootIndicator

theorem RawCompressionExecution.stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) + E.nonrootCount

theorem RawCompressionExecution.cost_eq_stepCostSum
    (E : RawCompressionExecution m n r) :
    E.cost = E.stepCostSum

theorem RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) + E.nonrootCount

theorem RawCompressionStep.projected_nonrootIndicators_add_le_nonrootIndicator
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    (S.bottomProjectedStep D hS cut hcut).nonrootIndicator +
        (S.topProjectedStep D hS cut hcut).nonrootIndicator <=
      S.nonrootIndicator

theorem RawCompressionExecution.projectedNonrootCounts_add_le_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.bottomProjectedNonrootCount hsteps D cut hcut +
        E.topProjectedNonrootCount hsteps D cut hcut <=
      E.nonrootCount

theorem RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
          E.topProjectedNonrootCount hsteps D (E.dissectionCut hsteps D)
            (E.dissectionCut_spec hsteps D)
```

Representative next statement:

```lean
theorem projected_step_commutes_with_restriction
    {n r : Nat}
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    -- bottom/top restricted before/after states and projected paths form
    -- valid projected steps, with cost/count accounting for this step.
    Prop
```

## Blocker Classification

Primary blocker: execution projection and restriction commutation.

Secondary blockers:

- nonrootpath counting for projected executions;
- replacing the current execution-level `+ E.nonrootCount` boundary term by
  the paper's sharper `+ card Xb + nonrootCount Ct` accounting;
- deriving the rank-forest top-cardinality packing from a concrete child or
  subtree property.

The rank arithmetic itself is now available in Nat-friendly form once a
`RankThresholdDissection.TopPacking` witness is supplied:

```lean
theorem RankThresholdDissection.top_card_mul_pow_le :
    (dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n

theorem RankThresholdDissection.top_card_le_div :
    (dissection F hF s).topFinset.card <= n / 2 ^ (s + 1)
```

## Main Lemma Status

The paper/lecture main lemma remains unproved in Lean:

```lean
theorem projected_nonroot_count_le :
    nonrootCount Cb + nonrootCount Ct <= nonrootCount C

theorem source_main_lemma_cost :
    Cost C <= Cost Cb + Cost Ct + card Xb + nonrootCount Ct
```

The current branch proves a raw-execution precursor:

```lean
theorem RawCompressionExecution.stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount :
    E.stepCostSum <= bottomProjectedCostSum + topProjectedCostSum + E.nonrootCount

theorem RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_nonrootCount :
    E.cost <= bottomProjectedCostSum + topProjectedCostSum + E.nonrootCount

theorem RawCompressionExecution.projectedNonrootCounts_add_le_nonrootCount :
    bottomProjectedNonrootCount + topProjectedNonrootCount <= E.nonrootCount

theorem RawCompressionExecution.cost_le_canonicalProjectedCostSums_add_topProjectedNonrootCount :
    E.cost <= bottomProjectedCostSum + topProjectedCostSum + topProjectedNonrootCount
```

This is weaker than the paper cost lemma and still uses per-step projected
objects, not projected executions `Cb` and `Ct`.

## Next Smallest Worker Theorem

The next smallest useful theorem is to define projected executions over the
restricted bottom/top forests and prove their consecutive-state commutation.
Recommended next target:

```lean
theorem projected_execution_commutes_with_restriction
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hD : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).afterDissection (D i) (hE.1 i) = D j) :
    -- the bottom/top per-step projections assemble into consecutive
    -- restricted executions, with the cost sums from
    -- `stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount`.
    Prop
```

After that, sharpen the boundary accounting from source nonrootpath count to
the paper's `card Xb + nonrootCount Ct` term, then connect the projected
executions to the recurrence parameters.

## Honesty Boundary

This branch does not alter the constants or packet normalizations:

```text
R_{z+1}(Q) >= A(z,4Q)
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
alphaJQ <= alphaQ + 1
alphaJS <= alphaQ + 2
(alphaQ m n + 3) * m + 4 * n
```

No new field was added to `topDownCost`, `SourceModel`, or
`RawCompressionExecution.HasBaseRankAccounting`.
