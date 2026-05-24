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

## Continuation Progress

A continuation pass added the charged-slot enumeration API that was identified
below as the first obstruction:

```lean
theorem RawCompressionPath.ProjectedCompressionStep
    .nonrootIndicator_eq_one_of_charged

theorem RawCompressionPath.ProjectedCompressionStep
    .nonrootIndicator_eq_zero_of_not_charged

noncomputable def RawCompressionPath.ProjectedCompressionExecution
    .chargedFinset

theorem RawCompressionPath.ProjectedCompressionExecution
    .chargedFinset_card_eq_chargedCount

noncomputable def RawCompressionPath.ProjectedCompressionExecution
    .chargedSlot

theorem RawCompressionPath.ProjectedCompressionExecution
    .chargedSlot_isCharged

theorem RawCompressionPath.ProjectedCompressionExecution
    .chargedSlot_strictMono

noncomputable def RawCompressionExecution
    .rankThresholdTopChargedSlot

theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_isCharged

theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_strictMono

theorem RawCompressionPath.ProjectedPathSegment
    .node_injective_of_nonroot

theorem RawCompressionPath.ProjectedPathSegment
    .len_le_card_of_nonroot

theorem RawCompressionExecution
    .rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged

theorem RawCompressionExecution
    .rankThreshold_topProjected_charged_path_lifts_to_padded_path
```

Thus the compacted top slots now have an increasing map

```lean
Fin Ct.chargedCount -> Fin m
```

and each selected slot is proved charged.

In addition, every charged rank-threshold top projected step is proved to have
top-projection length at most the external padded top budget. This discharges
the active-length side of the eventual `RawCompressionPath` lifting into
`Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)`.

The same pass also added a cost-only path lift: every charged top projected
step can be packaged as an ordinary `RawCompressionPath` over the padded top
budget with matching edge cost. This does not yet prove parent-chain validity
or the rewiring fields for the padded top step.

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

The first remaining obstruction on the direct route is the charged-subsequence
execution construction over `Fin Ct.chargedCount`.

The existing projected execution `Ct` is indexed by all source slots `Fin m`,
while the recurrence term uses the compacted count of charged top slots:

```lean
Ct.chargedCount
```

The order-preserving enumeration now exists:

```lean
E.rankThresholdTopChargedSlot hE s :
  Fin Ct.chargedCount -> Fin m
```

The next missing theorem is the consecutive-state theorem for the charged-only
subsequence. The new identity lemma for uncharged top projected steps is the
local ingredient that should make skipped uncharged slots transparent.

After that charged-subsequence theorem, the next obstructions are:

- Path lifting: the cost-only `RawCompressionPath` packaging is now proved.
  The remaining work is to strengthen it to parent-chain validity against the
  padded top forest, identify the padded target, and prove the rewiring fields
  for the transported step.
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

The charged-slot theorem is now proved:

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
theorem rankThresholdTopChargedSlot_isCharged :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    forall q,
      (Ct.step (rankThresholdTopChargedSlot E hE s q)).IsCharged
```

The smallest next theorem is now the charged-subsequence consecutive-state
bridge: for adjacent compacted charged indices `q` and `q'`, the after-parent
map of the source slot `E.rankThresholdTopChargedSlot hE s q` should agree
with the before-parent map of `E.rankThresholdTopChargedSlot hE s q'` after
transport across the stable top-side equivalence and across skipped uncharged
slots. The exact statement should be chosen together with the padded execution
constructor so its transported-equivalence target matches the later
`RawCompressionExecution.HasConsecutiveStates` proof.

The smallest local path-lifting theorem below is now proved in cost-only form:

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

The next path-lifting strengthening should add the parent-chain and target
fields needed by `RawCompressionPath.IsValidFor` for the padded
`RankThresholdDissection.topRestrictedForestFin ... |>.padRight ...`.

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

Ambition D achieved, with supporting Lean theorems for budgeted top
consumption, charged-slot enumeration, top-budget active length, and
cost-only padded path lifting. The padded top execution itself is not yet
constructed.
