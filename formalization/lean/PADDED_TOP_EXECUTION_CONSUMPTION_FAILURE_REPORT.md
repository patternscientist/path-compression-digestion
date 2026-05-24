# Padded Top Execution Consumption Failure Report

Branch: `lean-padded-top-execution-consumption-v1`

Starting base:

```text
main HEAD = f25158d3b4e2fbb37f41ce5ff2129f6c41cf8611
merged prerequisite = 960ed96ff55fe76cbec5308c8fcb6cb8f6c03701
```

## Summary

This worker did not construct the charged-slot padded top execution and did
not prove the full `RawCompressionExecution.RankThresholdJInputConsumableBounds`
package.

It did add three source-level support lemmas in `SourceProjection.lean`:

```lean
theorem RawCompressionStep
    .topProjectedStep_afterParent_eq_beforeParent_of_not_charged

theorem RawCompressionExecution
    .rankThreshold_source_cost_le_diamond_budget_of_topBudget_consumable_bounds

theorem RawCompressionExecution
    .rankThreshold_top_consumableCost_le_JInput_topBudget_of_topDownCost
```

The first lemma proves that a root-like, uncharged top projection is identity
on the top restricted parent map. This is the local fact needed to skip
uncharged top slots when building a charged-slot-only execution.

The second lemma is the budgeted top arithmetic consumer: if the top
consumable term is bounded with

```lean
RankThresholdDissection.topRestrictedBudget (n := n) s
```

instead of exact top cardinality, the existing source-shift target is still
obtained using

```lean
RawCompressionExecution.rankThresholdDissectionFamily_two_mul_topBudget_mul_g_le
```

The third lemma converts a future padded-top `topDownCost` domination theorem
into the concrete `JInput` top budget field using the previous-row source
bound.

## Exact Top Projected Execution

For

```lean
E : RawCompressionExecution m n r
hE : E.IsValid
s : Nat
```

the top projected execution whose consumable cost must be consumed is:

```lean
let Ct :=
  E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
Ct.consumableCost
```

At the `JInput` log cut, this specializes to:

```lean
let s := ceilLog2 ((JInput k).g r)
let Ct :=
  E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)
```

## Exact Padded Target

The intended ordinary padded execution target is:

```lean
RawCompressionExecution
  Ct.chargedCount
  (RankThresholdDissection.topRestrictedBudget (n := n) s)
  (r - s - 1)
```

At an original slot `i`, the padded before forest should be:

```lean
(RankThresholdDissection.topRestrictedForestFin
    (E.step i).before (hE.1 i).1.1 s).padRight
  (RankThresholdDissection.topRestrictedForestFin_card_le_budget
    (E.step i).before (hE.1 i).1.1
    ((E.hasRankThresholdPacking_of_isValid hE i).1) s)
```

The analogous after forest should use `(E.step i).after`, `(hE.1 i).2.1`,
and `((E.hasRankThresholdPacking_of_isValid hE i).2)`.

The external budget is the Lean definition:

```lean
RankThresholdDissection.topRestrictedBudget (n := n) s
```

not a hard-coded prose formula.

## First Obstruction

The first obstruction on the direct route is index lifting for the compacted
charged execution over `Fin Ct.chargedCount`.

The existing projected execution `Ct` is indexed by all source slots
`Fin m`, while the recurrence term uses the compacted count of charged top
slots:

```lean
Ct.chargedCount
```

The code does not yet have an order-preserving enumeration of the charged top
slots:

```lean
Fin Ct.chargedCount -> Fin m
```

nor the consecutive-state theorem for the charged-only subsequence. The new
identity lemma for uncharged top projected steps is the local ingredient that
should make this subsequence theorem true.

After index lifting, the next obstructions are:

- Path lifting: turn a charged `ProjectedPathSegment` over the dependent top
  node type into a `RawCompressionPath` over `Fin topBudget`.
- Semantic validity: prove the transported padded top step satisfies
  `RawCompressionStep.IsValid`, including the nonroot rewiring field.
- Base accounting: build the legacy injection for the charged top execution,
  not just rank-threshold packing. The existing padding lemmas supply the
  rank-packing part, but not the charge-unit injection.
- Cost domination: prove the charged-only padded execution has cost at least
  `Ct.consumableCost`.
- TopDownCost consumption: apply `RawCompressionExecution.cost_le_topDownCost`
  to the padded valid execution, then feed the result to the new
  `rankThreshold_top_consumableCost_le_JInput_topBudget_of_topDownCost`.

## Viable Strategy

Strategy A remains the clearest mathematical route, but it needs a small
charged-slot API first. Strategy B is viable once the charged-slot ordinary
execution exists, because the budgeted arithmetic and padded rank-packing
side are now available.

Strategy C is viable only as an internal consumer after a top-budget
`topDownCost` domination theorem has been proved. The new budgeted arithmetic
lemmas prepare that route but do not supply the missing source-realization
theorem.

## Smallest Next Theorem Statements

The smallest next charged-slot theorem is:

```lean
noncomputable def rankThresholdTopChargedSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) ->
      Fin m
```

with an order and chargedness specification:

```lean
theorem rankThresholdTopChargedSlot_spec :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    forall q,
      (Ct.step (rankThresholdTopChargedSlot E hE s q)).IsCharged
```

The smallest local path-lifting theorem after that is:

```lean
theorem rankThreshold_topProjected_charged_path_lifts_to_padded_path
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i)
        (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    Exists fun P :
      RawCompressionPath
        (RankThresholdDissection.topRestrictedBudget (n := n) s) =>
      P.cost =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i)
          (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost
```

The target source-realization theorem remains:

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

## Verdict

Ambition D achieved, with three supporting Lean theorems. The padded top
execution itself is not yet constructed.
