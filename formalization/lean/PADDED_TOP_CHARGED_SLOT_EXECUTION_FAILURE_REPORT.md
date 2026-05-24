# Padded Top Charged-Slot Execution Failure Report

Branch: `lean-padded-top-charged-slot-execution-v1`

Starting base:

```text
main HEAD = e60c205a49e8066347a3ea44837aa1af0e77cae0
previous partial worker = bcea778176ca18174d372da8156ab4fefb50aa73
```

## Summary

This worker did not construct the full ordinary padded charged-slot
`RawCompressionExecution` and did not prove the `topDownCost` consumption
field for the rank-threshold top projection.

It did add the charged-slot-indexed local package in `SourceProjection.lean`:

```lean
theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_zero_cost_afterParent_eq_beforeParent

theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step
```

The first theorem records the zero-cost charged case as a projected identity:
the projected after-parent equals the projected before-parent, so this slot is
semantically skippable in the dependent projected execution.  The second theorem
wraps the previous positive-cost padded source-step realization at the compacted
charged slot index.

## 1. Charged-Slot Representation Used

The exact charged-slot representation is the existing increasing map:

```lean
E.rankThresholdTopChargedSlot hE s :
  Fin
    ((E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) ->
    Fin m
```

Equivalently, if

```lean
let Ct :=
  E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
```

then this is `Ct.chargedSlot`, transported through the rank-threshold top
projection API.

The dependent charged projected execution remains:

```lean
E.rankThresholdTopChargedProjectedExecution hE s
```

with:

```lean
(E.rankThresholdTopChargedProjectedExecution hE s).HasConsecutiveStates

(E.rankThresholdTopChargedProjectedExecution hE s).cost =
  Ct.consumableCost
```

## 2. Zero-Cost Slots: Skip Or No-Op

The current proved representation treats zero-cost charged slots as skipped
slots at the projected parent-map level:

```lean
rankThresholdTopChargedSlot_zero_cost_afterParent_eq_beforeParent
```

This applies the existing local theorem:

```lean
RawCompressionStep.topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero
```

An ordinary `RawCompressionExecution` has no native skipped-slot constructor:
it is indexed by exactly `Fin m`, and every slot is a `RawCompressionStep`.
The ordinary model can represent a semantic no-op only as a valid rootpath step
with zero source cost and unchanged parent map.  The current API does not yet
provide the generic rootpath/no-op constructor needed to turn every zero-cost
charged projected slot into such a padded ordinary step with the correct
before-state.

Thus zero-cost charged slots are presently skippable in the projected execution
but not yet packaged as ordinary padded no-op source steps.

## 3. Exact State-Alignment Theorem Needed

For adjacent compacted charged slots `q` and `q'` with
`q.val + 1 = q'.val`, let:

```lean
let Ct :=
  E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
let i := E.rankThresholdTopChargedSlot hE s q
let j := E.rankThresholdTopChargedSlot hE s q'
let N := RankThresholdDissection.topRestrictedBudget (n := n) s
```

The ordinary padded execution needs the exact forest equality:

```lean
S_i.after =
  (RankThresholdDissection.topRestrictedForestFin
      (E.step j).before (hE.1 j).1.1 s).padRight
    (RankThresholdDissection.topRestrictedForestFin_card_le_budget
      (E.step j).before (hE.1 j).1.1
      ((E.hasRankThresholdPacking_of_isValid hE j).1) s)
```

where `S_i` is the ordinary padded step chosen for charged slot `q`.  The
existing projected theorem proves parent-map commutation across the dependent
top-node equivalence:

```lean
RawCompressionExecution.rankThresholdTopChargedSlot_after_commutes_with_next
```

but this has not yet been upgraded to literal equality of the padded
`RawRankedForest N (r - s - 1)` coordinates used by
`RawCompressionExecution.HasConsecutiveStates`.

## 4. RawCompressionExecution No-Op/Skipped Support

`RawCompressionExecution` supports only ordinary slots:

```lean
structure RawCompressionExecution (m n r : Nat) where
  step : Fin m -> RawCompressionStep n r
```

and consecutive states require literal equality:

```lean
forall i j : Fin m,
  i.val + 1 = j.val -> (E.step i).after = (E.step j).before
```

There is no skipped-slot representation.  Skipping zero-cost charged slots
would change the execution length away from `Ct.chargedCount`; to consume that
through the current `topDownCost` interface one would also need a monotonicity
or padding theorem for `topDownCost` in the execution-length argument.  Such a
theorem is not currently available.

The no-op route is therefore preferable, but it needs a generic padded
rootpath/no-op constructor and exact state alignment.

## 5. Legacy Base Accounting Obstruction

The positive-cost slot lift proves semantic validity and rank-threshold packing
for each local padded step:

```lean
S.IsValid
S.before.HasRankThresholdPacking
S.after.HasRankThresholdPacking
```

It does not construct the legacy charge-unit injection required by:

```lean
RawCompressionExecution.HasLegacyBaseRankAccounting
```

Consequently, even after assembling a semantically valid charged-slot padded
execution, the full validity predicate:

```lean
Etop.IsValid
```

would still require a charge injection:

```lean
Etop.ChargeUnit -> Prod (Fin (RankThresholdDissection.topRestrictedBudget (n := n) s))
  (Fin ((r - s - 1) - 1))
```

This is the legacy base charge injection gap identified by the previous worker.

## 6. Smallest Next Theorem Statement

The smallest next theorem is the exact ordinary after-forest strengthening of
the positive-cost local lift:

```lean
theorem rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step_with_after
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hpos :
      0 <
        ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = Gbefore.padRight hNbefore /\
        S.after = Gafter.padRight hNafter /\
        S.cost =
          ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
        S.before.HasRankThresholdPacking /\
        S.after.HasRankThresholdPacking
```

After this, the assembly theorem can use
`rankThresholdTopChargedProjectedExecution_hasConsecutiveStates` to prove
literal padded consecutive-state equality, provided the top-node equivalence is
shown to coincide with the `topRestrictedForestFin`/`padRight` coordinates.

## Verdict

Ambition D-plus achieved.  Positive and zero-cost compacted charged slots now
have explicit local theorems at the charged-slot index.  The ordinary padded
execution is still blocked by exact padded after-state alignment and the legacy
base charge injection.
