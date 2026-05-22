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
- `RawCompressionPath.activeFinset`
- `RawCompressionPath.properFinset`
- `RawCompressionPath.projectedActiveFinset`
- `RawCompressionPath.projectedProperFinset`
- `RawCompressionPath.HasDissectionCut`
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

The first theorem not yet closed is the construction of actual bottom/top
projected path objects over restricted forests, with parent-chain proofs:

```lean
theorem bottom_projected_path_is_valid
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    -- the bottom projection is a valid path in the restricted bottom forest.
    Prop

theorem top_projected_path_is_valid
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    -- the top projection is a valid path in the restricted top forest.
    Prop
```

These statements are not in Lean yet because the existing `RawCompressionPath`
type stores paths in fixed `Fin n` arrays, while the natural projected paths
live over restricted bottom/top vertex types.  This branch defines projected
active/proper index sets and proves the existence of the dissection cut; it
does not yet define projected path objects carrying their own targets,
rootpath/nonrootpath classification, and restricted parent-chain proofs.

## Blocker Classification

Primary blocker: projected path object construction.

Secondary blockers:

- execution/restriction commutation;
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

The next smallest useful theorem is to define the projected path objects
associated to a cut and prove their parent-chain facts.  Recommended next
target:

```lean
theorem bottom_projected_path_parent_chain
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    -- adjacent active bottom-projection slots follow `RawDissection.bottomParent`.
    Prop
```

The analogous top parent-chain theorem should follow from upward closure and
`RawDissection.topParent`.  After those two path-level facts, prove
execution/restriction commutation for one step before lifting to sequences.

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
