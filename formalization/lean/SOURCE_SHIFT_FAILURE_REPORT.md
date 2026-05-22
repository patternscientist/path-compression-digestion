# Source Shift Failure Report

Branch: `lean-source-shift-main-lemma-v1`

Starting commit: `4d6febfe0ea9cd10cc99d73d029e3491f5b63a8a`

## Summary

This branch adds the first source-dissection Lean module:

```text
PathCompressionDigestion/SourceDissection.lean
```

The module formalizes concrete dissection structure around the existing
`ConcreteSourceModel` API, including bottom/top membership, restricted
bottom/top parent maps, local path-contiguity across a dissection, raw
nonrootpath counting, and rank-threshold dissection facts.

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

It also packages actual projected one-step objects:

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

Primary blocker: step/execution projection and restriction commutation.

Secondary blockers:

- nonrootpath counting for projected executions;
- cost accounting for cross-side parent changes;
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

The current branch prepares the vocabulary for these theorem statements but
does not yet define `Cb` and `Ct` as executable projected compression
sequences over restricted forests.

## Next Smallest Worker Theorem

The next smallest useful theorem is to define restricted before/after forest
objects for one raw step and prove the projected segments commute with the
single-step parent update.  Recommended next target:

```lean
theorem projected_step_commutes_with_restriction
    {n r : Nat}
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    -- the bottom/top restricted projected steps are valid and preserve the
    -- path-level accounting supplied by
    -- `RawCompressionPath.sourceCost_le_projection_edgeCosts_add_one`.
    Prop
```

After that, lift the one-step construction to `RawCompressionExecution`, prove
the charge-unit execution cost equals the sum of step costs, and then sum the
one-step projected-step inequalities.  A direct attempt at this summation was
left out of the branch because it made `SourceDissection.lean` compile too
slowly; the next worker should make that proof in a small auxiliary lemma or
module with a performance-conscious statement.

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
