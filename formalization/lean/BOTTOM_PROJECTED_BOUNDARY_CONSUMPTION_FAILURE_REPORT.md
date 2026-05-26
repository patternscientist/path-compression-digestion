# Bottom Projected Boundary-Consumption Failure Report

Branch: `lean-bottom-projected-boundary-consumption-v1`

Starting base:

```text
6ed3a2c12cccd749d69dc3a929e06afbd20b14ee
Add boundary-inclusive bottom slot skeleton report
```

## Summary

This pass followed the direct projected-accounting route and avoided packaging
source-relevant boundary exceptions as ordinary bottom `RawCompressionStep`s.
The first pass added two checked Lean theorems:

```lean
RawCompressionExecution
  .rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost

RawCompressionExecution
  .rankThresholdBottom_consumable_add_boundary_le_chargedProjected_add_bottomCard
```

These prove the projected split and boundary-card consumption part:

```text
bottom consumable cost + source-relevant bottom boundary cost
  <= charged bottom projected cost + stable bottom card
```

The route does not close `RankThresholdJInputBottomConsumableBounds`, because
the remaining charged projected cost still needs a recurrence-consumption bound.
The available recurrence interface `topDownCost` applies to valid ordinary
`RawCompressionExecution`s, not directly to a projected execution.  The old
charged-only ordinary skeleton cannot currently supply that bridge because its
consecutive-state theorem is the known false/wrong-object target.

Continuation update: the remaining charged-projected obligation is now named
and connected to the existing bottom and shift bridges by checked Lean:

```lean
RawCompressionExecution.RankThresholdJInputBottomChargedProjectedBounds
RawCompressionExecution
  .rankThresholdJInputBottomConsumableBounds_of_chargedProjectedBounds
RawCompressionExecution
  .topDown_shift_step_of_rankThresholdJInputBottomChargedProjectedBounds
```

Thus the bottom projected boundary-consumption work has been reduced to the
single charged projected recurrence bound; the boundary-card contribution is no
longer part of the gap.

Second continuation update: the fallback boundary-inclusive skeleton route now
has its first checked skip-safety lemma.  Any rank-threshold bottom slot omitted
by `rankThresholdBottomRelevantSlot` is a literal no-op on the bottom restricted
parent map:

```lean
RawCompressionStep
  .bottomProjectedStep_afterParent_eq_beforeParent_of_no_sourceBoundary

RawCompressionExecution
  .rankThresholdBottomProjectedStep_afterParent_eq_beforeParent_of_not_relevant
```

This identifies the boundary-inclusive relevant-slot enumeration as the right
object for consecutive-state alignment: charged slots and source-relevant
boundary exceptions are kept, while every skipped slot is now known to preserve
the bottom projected parent map.

Third continuation update: the projected boundary-inclusive consecutive-state
gap is now closed.  The following checked Lean objects compose the skipped
non-relevant no-ops across intervals between adjacent relevant slots:

```lean
RawCompressionExecution
  .rankThresholdDissectionFamily_bottomStable_of_slot

RawCompressionExecution
  .rankThresholdBottomProjectedStep_after_commutes_with_later_before_of_not_relevant_between

RawCompressionExecution
  .rankThresholdBottomRelevantSlot_after_commutes_with_next

RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution

RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_hasConsecutiveStates

RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_isSemanticallyValid

RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_isAdmissible
```

This is still a projected execution, not an ordinary `RawCompressionExecution`.
The `topDownCost` recurrence interface still requires ordinary valid source
steps, so the remaining fallback gap has moved from projected consecutive-state
alignment to ordinary realization/cost packaging for the relevant slots.

## 1. Exact Bottom Projected Consumable Cost Expression

The package field asks to bound:

```lean
(E.canonicalBottomProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).consumableCost
```

Inside `RankThresholdJInputBottomConsumableBounds`, this is:

```lean
let s := ceilLog2 ((JInput k).g r)
let i0 : Fin m := ⟨0, by omega⟩
let Cb :=
  E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
Cb.consumableCost <=
  (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s
```

## 2. Exact Charged Bottom Cost Expression

The charged bottom projected cost is:

```lean
(E.rankThresholdBottomChargedProjectedExecution hE s).cost
```

The new theorem exposes the existing equality in the direction needed for
direct accounting:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost =
      (E.rankThresholdBottomChargedProjectedExecution hE s).cost
```

The pre-existing ordinary charged skeleton cost equality is still:

```lean
RawCompressionExecution
  .rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost
```

but using it for `topDownCost` still requires semantic validity, hence
consecutive-state alignment.

## 3. Exact Boundary-Exception Cost/Cardinality Expression

The source-relevant bottom boundary-exception cost is:

```lean
E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
  (E.rankThresholdDissectionFamily hE.1 s)
```

It is counted by the existing finite edge-unit model:

```lean
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit
RawCompressionExecution.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum
```

The previous branch also added the slot predicate:

```lean
RawCompressionExecution.rankThresholdBottomBoundaryExceptionSlot
```

but the direct route in this pass does not need to enumerate or package those
slots as ordinary steps.

## 4. Exact Boundary-Card Accounting Theorem Used

The theorem used by the new direct projected bound is:

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

The new combined theorem is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottom_consumable_add_boundary_le_chargedProjected_add_bottomCard
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost + X <=
      (E.rankThresholdBottomChargedProjectedExecution hE s).cost + Bcard
```

## 5. Can Direct Projected Accounting Avoid Ordinary Boundary-Inclusive Execution?

Yes for the boundary contribution.  The source-relevant uncharged bottom
boundary exceptions can be kept in the projected accounting lane and paid by the
existing stable bottom-card theorem.  No ordinary boundary-inclusive execution
is needed for that part.

No for the full `RankThresholdJInputBottomConsumableBounds` field yet.  After
the direct split, the remaining obligation is still a recurrence-consumption
bound for:

```lean
(E.rankThresholdBottomChargedProjectedExecution hE s).cost
```

The current recurrence bridge still goes through ordinary `topDownCost`, which
requires a valid ordinary execution.  The available ordinary charged skeleton is
not known semantically valid because its consecutive-state alignment skips the
state-changing boundary exceptions.

## 6. Boundary-Exception Ordinary Realization Theorem Needed If Direct Route Fails

If the project returns to an ordinary boundary-inclusive skeleton, the needed
local theorem remains:

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
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking
```

This would also need a preservation theorem for skipped uncharged
non-source-relevant bottom slots; that preservation theorem is now supplied by:

```lean
RawCompressionExecution
  .rankThresholdBottomProjectedStep_afterParent_eq_beforeParent_of_not_relevant
```

and its multi-slot projected composition is now supplied by:

```lean
RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_hasConsecutiveStates
```

## 7. Smallest Next Theorem Statement

For the direct projected route, the smallest next theorem is now the named
charged projected recurrence-consumption boundary:

```lean
def RawCompressionExecution.RankThresholdJInputBottomChargedProjectedBounds
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      (k + 1) * Cb.chargedCount +
        2 * Bcard * (JInput k).diamond s
```

The new bridge theorem proves that this exact proposition closes
`RankThresholdJInputBottomConsumableBounds`:

```lean
theorem RawCompressionExecution
  .rankThresholdJInputBottomConsumableBounds_of_chargedProjectedBounds
    (k : Nat)
    (hcharged :
      RawCompressionExecution.RankThresholdJInputBottomChargedProjectedBounds k) :
    RawCompressionExecution.RankThresholdJInputBottomConsumableBounds k
```

and the existing padded-top shift bridge then gives:

```lean
theorem RawCompressionExecution
  .topDown_shift_step_of_rankThresholdJInputBottomChargedProjectedBounds
    (k : Nat)
    (hcharged :
      RawCompressionExecution.RankThresholdJInputBottomChargedProjectedBounds k) :
    topDownShiftStepTarget k
```

So the smallest next mathematical theorem can be stated either as the named
proposition above or as a theorem returning it:

```lean
theorem RawCompressionExecution
  .rankThresholdJInputBottomChargedProjectedBounds_closed
    (k : Nat) :
    RawCompressionExecution.RankThresholdJInputBottomChargedProjectedBounds k
```

For the boundary-inclusive skeleton fallback, the multi-slot projected
commutation theorem for adjacent relevant slots is now proved:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomRelevantSlot_after_commutes_with_next
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {q q' : Fin (E.rankThresholdBottomRelevantCount hE s)}
    (hqq' : q.val + 1 = q'.val) :
    let Dfam := E.rankThresholdDissectionFamily hE.1 s
    let i := E.rankThresholdBottomRelevantSlotEnum hE s q
    let j := E.rankThresholdBottomRelevantSlotEnum hE s q'
    ((E.step i).bottomProjectedStep
      (Dfam i) (hE.1 i)
      (E.dissectionCut hE.1 Dfam i)
      (E.dissectionCut_spec hE.1 Dfam i)).ParentCommutesWithEquiv
      ((E.step j).bottomProjectedStep
        (Dfam j) (hE.1 j)
        (E.dissectionCut hE.1 Dfam j)
        (E.dissectionCut_spec hE.1 Dfam j))
      ((Dfam i).bottomEquivOfBottomIff (Dfam j)
        (E.rankThresholdDissectionFamily_bottomStable_of_slot
          hE.1 hE.2.1 s i j))
```

The smallest next fallback theorem is now the ordinary realization theorem for
source-relevant bottom boundary-exception slots, with matching before/after
restricted forests and a cost that can be charged to the existing boundary-card
term:

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
            S.cost <=
              (E.step i).sourceRelevantBottomExceptionalCost
                D (hE.1 i)
                (E.dissectionCut hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i) /\
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking
```

## Verdict

Ambition C achieved for direct projected boundary accounting.  The projected
bottom decomposition and boundary-card bound are proved without an ordinary
boundary-inclusive execution.  The fallback boundary-inclusive route now has
the checked projected relevant-slot consecutive-state composition, but it still
lacks ordinary boundary-exception realization/cost packaging.  Ambition B
remains blocked by the charged projected recurrence-consumption bridge.
