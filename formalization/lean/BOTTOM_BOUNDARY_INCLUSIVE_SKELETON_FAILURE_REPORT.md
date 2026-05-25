# Bottom Boundary-Inclusive Skeleton Failure Report

Branch: `lean-bottom-boundary-inclusive-skeleton-v1`

Starting base:

```text
ea642b45f6a75ab6ccb3e9dfbeffb2055b42a095
Add bottom charged execution skeleton
```

## Summary

This pass added the first-class boundary-inclusive slot layer in Lean:

```lean
RawCompressionExecution.rankThresholdBottomBoundaryExceptionSlot
RawCompressionExecution.rankThresholdBottomRelevantSlot
RawCompressionExecution.rankThresholdBottomRelevantFinset
RawCompressionExecution.rankThresholdBottomRelevantCount
RawCompressionExecution.rankThresholdBottomRelevantSlotEnum
RawCompressionExecution.not_rankThresholdBottomRelevantSlot_of_between_relevantSlotEnum_succ
```

The charged-only skeleton was not extended into a valid ordinary bottom
execution.  The remaining obstruction is not slot enumeration; it is the absent
ordinary-step realization theorem for source-relevant uncharged bottom boundary
transitions, plus the complementary preservation theorem for skipped
non-relevant uncharged bottom slots.

## 1. Exact Source-Relevant Boundary Exception Predicate

The predicate added in this branch is:

```lean
def RawCompressionExecution.rankThresholdBottomBoundaryExceptionSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) : Prop :=
  (E.step i).path.IsNonrootPath (E.step i).before /\
    Not ((E.step i).bottomProjectedStep
      (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
      (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
      (E.dissectionCut_spec hE.1
        (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged /\
    Exists fun q : Fin (n + 1) =>
      q.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i
```

This is the slot-level version of the existing edge-unit predicate:

```lean
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit
```

The boundary-inclusive predicate used by the new enumeration is:

```lean
def RawCompressionExecution.rankThresholdBottomRelevantSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) : Prop :=
  ((E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)).step i).IsCharged \/
    E.rankThresholdBottomBoundaryExceptionSlot hE s i
```

## 2. Exact Existing Boundary-Card Accounting Theorem

The source-relevant bottom exceptional cost is already bounded by the stable
bottom boundary side:

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

It is consumed by:

```lean
theorem RawCompressionExecution
  .rankThreshold_source_cost_le_projected_consumable_add_boundary
```

The proof route goes through the finite edge-unit injection:

```lean
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeVertex_injective
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_le_bottomFinset_card
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum
```

## 3. Exact State-Changing Uncharged Bottom Step Theorem Needed

To package boundary slots as ordinary bottom steps, the missing theorem is an
exact before/after realization theorem for source-relevant boundary exceptions:

```lean
theorem RawCompressionExecution
  .rankThreshold_bottomBoundaryExceptionSlot_lifts_to_valid_step_with_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hboundary :
      E.rankThresholdBottomBoundaryExceptionSlot hE s i) :
    let D := E.rankThresholdDissectionFamily hE.1 s i
    let Gbefore :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let Gafter :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    Exists fun S : RawCompressionStep D.bottomFinset.card s =>
      S.IsValid /\
        S.before = Gbefore /\
          S.after = Gafter /\
            S.cost =
              (E.step i).sourceRelevantBottomExceptionalCost D (hE.1 i)
                (E.dissectionCut hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i) /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking
```

This theorem may require a new transition model rather than a standard
`RawCompressionStep`: a boundary exception can change a bottom restricted parent
to a self-parent when the raw after-parent crosses to the top side.  The current
ordinary valid-step constructors only provide nonroot compression steps and
zero-cost no-op root steps.

The skipped-slot preservation theorem also remains missing:

```lean
theorem RawCompressionStep
  .bottomProjectedStep_afterParent_eq_beforeParent_of_not_charged_not_sourceRelevant
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnotCharged : Not (S.bottomProjectedStep D hS cut hcut).IsCharged)
    (hnotRelevant :
      Not (S.path.IsNonrootPath S.before /\
        Exists fun q : Fin (n + 1) => q.val + 1 < cut)) :
    (S.bottomProjectedStep D hS cut hcut).afterParent =
      (S.bottomProjectedStep D hS cut hcut).beforeParent
```

## 4. Generalize Or Replace The Current Charged Skeleton?

The current charged-slot skeleton should be replaced by a boundary-inclusive
skeleton if the boundary-transition theorem above is true.  The enumeration
piece can be generalized safely, and this branch does so for the slot layer.

If source-relevant boundary exceptions cannot be represented as ordinary
`RawCompressionStep`s over the bottom restricted forest, then the ordinary
bottom skeleton should not be forced.  The sound alternative is to consume:

```text
charged bottom projected consumable cost
+ source-relevant bottom exceptional boundary cost
```

directly through projected execution plus the existing boundary-card accounting.

## 5. Exact Cost Inequality Needed After Adding Boundary Slots

A successful boundary-inclusive ordinary skeleton would need the following cost
decomposition:

```lean
let Cb :=
  E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
let X :=
  E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
let Brel := E.rankThresholdBottomBoundaryInclusiveExecutionSkeleton hE s i0
Brel.cost = Cb.consumableCost + X
```

Then the boundary-card theorem supplies:

```lean
X <= ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

The remaining `JInput` bottom bound would need the arithmetic bridge:

```lean
Cb.consumableCost <=
  (k + 1) * Cb.chargedCount +
    2 * ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
      (JInput k).diamond s
```

The charged-only cost equality remains available:

```lean
RawCompressionExecution.rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost
```

but it is conditional for recurrence consumption because the charged-only
skeleton still lacks consecutive-state alignment.

## 6. Smallest Next Theorem Statement

The smallest next theorem is the skipped-slot preservation theorem specialized
to rank-threshold execution intervals with no boundary-inclusive relevant slot:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomParent_eq_later_beforeParent_of_not_relevant_between
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i j : Fin m}
    (hij : i.val < j.val)
    (hskip :
      forall k : Fin m, i.val < k.val -> k.val < j.val ->
        Not (E.rankThresholdBottomRelevantSlot hE s k)) :
    forall v : (E.rankThresholdDissectionFamily hE.1 s i).BottomNode,
      (E.step i).after.parent v.1 = (E.step j).before.parent v.1
```

After that, the next theorem is the boundary-slot valid-step realization in
section 3.  Those two statements are the narrow bridge from the new relevant
slot enumeration to a genuine consecutive ordinary bottom execution.

## Verdict

Ambition D achieved, with partial Ambition C infrastructure: the
boundary-inclusive slot predicate and ordered enumeration are present and
mechanically checked.  Boundary exceptions are not yet packaged as ordinary
bottom steps, and global consecutive-state alignment for a boundary-inclusive
ordinary skeleton remains open.
