# Budgeted Top Restricted Realization Failure Report

Branch: `lean-budgeted-top-restricted-realization-v1`

Starting base:

```text
origin/main = 2de9cfa9f6760302f28205881b1fdd5461910798
requested prerequisite present = 5bb9b34885e404c644bcd64c34e619ac395aa0e7
```

## Summary

This worker did not prove the full top consumable simulation bound and did not
prove:

```lean
theorem rankThresholdJInputConsumableBounds :
    forall k : Nat,
      RawCompressionExecution.RankThresholdJInputConsumableBounds k
```

It did formalize the budgeted/padded rank side of the intended repair.  The
top restricted shifted forest is now proved to satisfy rank-threshold packing
against the external Seidel--Sharir budget

```lean
RankThresholdDissection.topRestrictedBudget (n := n) s
  = n / 2 ^ (s + 1)
```

and padding that forest into the external budget gives an ordinary
rank-threshold-packing forest.

## Exact Top Restricted Object

For a valid source execution

```lean
E : RawCompressionExecution m n r
hE : E.IsValid
s : Nat
```

the top projected object whose consumable cost must be consumed is:

```lean
let Ct :=
  E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
Ct.consumableCost
```

The concrete shifted top forest at a slot `i` is:

```lean
RankThresholdDissection.topRestrictedForestFin
  (E.step i).before (hE.1 i).1.1 s
```

This forest has exact vertex count

```lean
(E.rankThresholdDissectionFamily hE.1 s i).topFinset.card
```

but exact-cardinality rank-threshold packing for this shifted forest is false.

## Target `topDownCost` Term And Budget

The sound budgeted target is:

```lean
topDownCost
  Ct.chargedCount
  (RankThresholdDissection.topRestrictedBudget (n := n) s)
  (r - s - 1)
```

not the exact-cardinality term

```lean
topDownCost Ct.chargedCount
  ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card)
  (r - s - 1)
```

The exact-cardinality term would require rank-threshold packing at the exact
top side size, which the current diagnostic refutes.  The budgeted term uses
the same budget as the source top-packing estimate:

```lean
n / 2 ^ (s + 1)
```

## Why The Budget Avoids The False Theorem

The false theorem would say:

```lean
(RankThresholdDissection.topRestrictedForestFin F hF s).HasRankThresholdPacking
```

with respect to the exact top cardinality.  The existing theorem

```lean
RankThresholdDissection.exists_topRestrictedForestFin_without_rankThresholdPacking
```

shows this is not derivable from ambient rank-threshold packing.

The budgeted replacement proved on this branch is:

```lean
theorem RankThresholdDissection
    .topRestrictedForestFin_hasRankThresholdPackingWithBudget
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (topRestrictedForestFin F hF s).HasRankThresholdPackingWithBudget
      (topRestrictedBudget (n := n) s)
```

The proof uses ambient packing at thresholds `s + t + 1`: a shifted top vertex
with shifted rank greater than `t` has ambient rank greater than `s + t + 1`,
so its count is paid by the larger ambient forest.  Division by `2^(s+1)`
produces the external top budget.

The branch also proves:

```lean
theorem RankThresholdDissection
    .topRestrictedForestFin_padded_hasRankThresholdPacking
```

which pads the shifted top forest with rank-zero roots up to the external
budget and obtains ordinary `HasRankThresholdPacking` for the padded forest.

## Best Next Repair

The best next repair is Strategy B: padding / embedding.

The rank side is now available, but the projected top execution is still a
dependent projected execution, not an ordinary `RawCompressionExecution` on a
fixed padded vertex type.  The next step should construct a padded ordinary
execution over

```lean
Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)
```

whose source cost dominates `Ct.consumableCost`, and whose validity uses the
new padded rank-validity and rank-packing certificates.

Strategy C, a direct top consumable bound, is also plausible after replacing
the top-side package boundary with the budgeted term.  This branch proves the
needed budget arithmetic:

```lean
theorem RankThresholdDissection.two_mul_topRestrictedBudget_mul_le

theorem RawCompressionExecution
    .rankThresholdDissectionFamily_two_mul_topBudget_mul_g_le
```

so the budgeted top term is small enough for the existing source-shift
boundary arithmetic.

## Smallest Next Theorem Statement

The smallest next source-realization theorem is:

```lean
theorem rankThreshold_topProjectedExecution_consumableCost_le_topDownCost_topBudget
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    Ct.consumableCost <=
      topDownCost
        Ct.chargedCount
        (RankThresholdDissection.topRestrictedBudget (n := n) s)
        (r - s - 1)
```

A useful constructive version would expose the padded witness:

```lean
theorem topRestrictedExecution_embeds_in_budgeted_valid_execution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    Exists fun Etop :
      RawCompressionExecution Ct.chargedCount
        (RankThresholdDissection.topRestrictedBudget (n := n) s)
        (r - s - 1) =>
      Etop.IsValid /\ Ct.consumableCost <= Etop.cost
```

After that theorem, the top field should be consumed by `hprev`; the package
boundary should use the top budget rather than exact `Tcard`, with the
budgeted arithmetic theorem above replacing the exact-top-cardinality boundary
term in the final shift calculation.

## Verdict

Ambition C achieved.  Budgeted rank packing and padded forest rank packing are
proved for the shifted top restriction.  The remaining blocker is the actual
cost/source-execution realization: turning the dependent top projected
execution into a valid padded `RawCompressionExecution` with cost at least
`Ct.consumableCost`.
