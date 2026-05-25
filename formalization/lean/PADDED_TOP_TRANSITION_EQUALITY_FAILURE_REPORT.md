# Padded Top Transition Equality Failure Report

Branch: `lean-padded-top-transition-equality-v1`

Starting base:

```text
main HEAD = 7b371e0be724a20b7ef1100611694971101ca6bc
contains = e60c205a49e8066347a3ea44837aa1af0e77cae0
contains = 79210d297513b2bea6ea0cf93db0d492f86a1152
```

## Summary

This worker did not prove the exact positive-slot padded after-forest equality
and did not assemble the charged-slot padded `RawCompressionExecution`.

The current positive-cost slot theorem is strong enough to produce a valid
ordinary padded step with exact before-state equality, exact cost equality, and
rank-threshold packing on both endpoint forests.  It is still too weak for
execution assembly because it does not expose the exact ordinary after forest.

## 1. Exact Current Theorem That Is Too Weak

The local theorem used by the charged-slot wrapper is:

```lean
theorem RawCompressionExecution
    .rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
```

The charged-slot-indexed wrapper is:

```lean
theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step
```

Both expose the following data:

```lean
Exists fun S : RawCompressionStep N (r - s - 1) =>
  S.IsValid /\
    S.before = G.padRight hN /\
      S.cost = projectedSlot.cost /\
        S.before.HasRankThresholdPacking /\
          S.after.HasRankThresholdPacking
```

The missing field is:

```lean
S.after = padded projected/rank-threshold after-state
```

Without this equality, adjacent charged slots cannot be turned into
`RawCompressionExecution.HasConsecutiveStates`, whose statement requires
literal equality:

```lean
forall i j : Fin m,
  i.val + 1 = j.val -> (E.step i).after = (E.step j).before
```

## 2. Exact Missing Equality Field

For a positive-cost charged top slot:

```lean
let Dfam := E.rankThresholdDissectionFamily hE.1 s
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
```

the desired strengthening is:

```lean
Exists fun S : RawCompressionStep N (r - s - 1) =>
  S.IsValid /\
    S.before = Gbefore.padRight hNbefore /\
    S.after = Gafter.padRight hNafter /\
    S.cost =
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
    S.before.HasRankThresholdPacking /\
    S.after.HasRankThresholdPacking
```

The zero-cost companion should identify the padded projected after-state with
the padded before-state.  The current theorem:

```lean
theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_zero_cost_afterParent_eq_beforeParent
```

proves this only at the dependent projected parent-map level:

```lean
((E.rankThresholdTopChargedProjectedExecution hE s).step q).afterParent =
  ((E.rankThresholdTopChargedProjectedExecution hE s).step q).beforeParent
```

It does not yet lift that parent-map equality to literal equality of padded
`RawRankedForest N (r - s - 1)` values.

## 3. Nature Of The Obstruction

The obstruction is not budgeted rank packing and not positive-cost step
validity.  Those are already available.

The obstruction is a projection/padding mismatch plus insufficient API access.

The positive lift builds its ordinary step by calling:

```lean
RawCompressionPath.exists_valid_step_of_valid_nonroot_path
```

on a locally constructed lifted `RawCompressionPath` over:

```lean
Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)
```

That generic constructor defines the ordinary after forest by:

```lean
parent := fun v =>
  if P.IsCompressedVertex v then F.parent P.target else F.parent v
rank := F.rank
```

To prove that this after forest is the padded rank-threshold top restriction
of `(E.step i).after`, Lean needs to know exactly which padded vertices satisfy
`P.IsCompressedVertex`.  The current API does not expose a theorem connecting
compressed vertices of the lifted padded path to compressed vertices in the
original raw source path/top projected segment.

There is a second coordinate issue: `topRestrictedForestFin` uses

```lean
(RankThresholdDissection.dissection F hF s).topNodeEquivFin
```

and therefore its concrete `Fin` coordinates are derived from the slot's
`topFinset`.  Even though a valid raw step preserves ranks, the before and
after top restrictions are not definitionally the same object.  Turning
projected parent-map commutation into literal padded-forest equality requires
an explicit coordinate compatibility theorem for `topNodeEquivFin` under the
rank-preserving top-finset equality.

Thus the missing proof is not a simple definitional equality; it needs two API
bridges:

1. lifted-path compressed-vertex characterization;
2. top-restricted coordinate compatibility across rank-preserving before/after
   forests.

## 4. Smallest Next Theorem Statement

The smallest useful next step is to factor the lifted positive top path out of
the current local proof into a reusable definition, then prove its compressed
vertices are exactly the embedded non-target vertices of the top projected
segment.

A precise next theorem shape is:

```lean
theorem rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost)
    (v : Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)) :
    (rankThresholdTopProjectedPaddedPath E hE s i hcharged hpos).IsCompressedVertex v <->
      Exists fun a :
        Fin
          ((E.step i).path.topProjectionLength
            (E.rankThresholdDissectionFamily hE.1 s i)
            (E.dissectionCut hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)) =>
        a.val + 1 <
          ((E.step i).path.topProjectionLength
            (E.rankThresholdDissectionFamily hE.1 s i)
            (E.dissectionCut hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)) /\
        v =
          -- the same top-node embedding used by the positive lift
          ...
```

Once that bridge exists, the direct state-equality theorem should be:

```lean
theorem rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step_with_state_eq
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

For zero-cost slots, after the coordinate compatibility theorem is available,
the companion theorem should be:

```lean
theorem rankThresholdTopChargedSlot_zero_cost_padded_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hcost :
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost = 0) :
    -- padded projected after-state for slot q =
    -- padded projected before-state for slot q
    ...
```

## Verdict

Ambition D achieved.  The exact after-state strengthening is blocked by missing
lifted-path compressed-vertex and coordinate-compatibility APIs, not by the
rank budget, charged-slot enumeration, or positive-step validity.
