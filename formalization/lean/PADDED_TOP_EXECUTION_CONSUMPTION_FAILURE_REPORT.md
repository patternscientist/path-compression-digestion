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

theorem RawCompressionPath.ProjectedCompressionExecution
    .not_isCharged_of_between_chargedSlot_succ

noncomputable def RawCompressionPath.ProjectedCompressionExecution
    .chargedSubexecution

theorem RawCompressionPath.ProjectedCompressionExecution
    .chargedSubexecution_cost_eq_consumableCost

theorem RawCompressionExecution
    .rankThresholdDissectionFamily_topStable_of_slot

theorem RawCompressionExecution
    .rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between

theorem RawCompressionExecution
    .rankThresholdTopProjectedStep_after_commutes_with_later_before_of_not_charged_between

theorem RawCompressionExecution
    .rankThresholdTopChargedSlot_after_commutes_with_next

noncomputable def RawCompressionExecution
    .rankThresholdTopChargedProjectedExecution

theorem RawCompressionExecution
    .rankThresholdTopChargedProjectedExecution_hasConsecutiveStates

theorem RawCompressionExecution
    .rankThresholdTopChargedProjectedExecution_isSemanticallyValid

theorem RawCompressionExecution
    .rankThresholdTopChargedProjectedExecution_isAdmissible

theorem RawCompressionExecution
    .rankThresholdTopChargedProjectedExecution_cost_eq_consumableCost

theorem RankThresholdDissection
    .topRestrictedForestFin_padded_parent_of_topNode

theorem RawCompressionExecution
    .rankThreshold_topProjected_charged_path_lifts_to_padded_valid_path

theorem RawCompressionStep
    .topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero

theorem RawCompressionExecution
    .rankThreshold_topProjected_charged_positive_path_lifts_to_padded_valid_path

theorem RawRankedForest
    .hasRankThresholdPacking_of_rankNat_eq

theorem RawCompressionPath
    .rankNat_lt_parent_target_of_compressedVertex_of_nonroot

theorem RawCompressionPath
    .exists_valid_step_of_valid_nonroot_path

theorem RawCompressionExecution
    .rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
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

A later continuation pass discharged the charged-subsequence obstruction at
the dependent projected-execution level. Adjacent compacted charged slots now
have consecutive projected states after skipped uncharged top slots, using
`topProjectedStep_afterParent_eq_beforeParent_of_not_charged`. The resulting
object is:

```lean
E.rankThresholdTopChargedProjectedExecution hE s
```

with:

```lean
(E.rankThresholdTopChargedProjectedExecution hE s).IsSemanticallyValid
(E.rankThresholdTopChargedProjectedExecution hE s).cost =
  Ct.consumableCost
```

This is still a dependent projected execution, not yet the ordinary padded
`RawCompressionExecution` over `Fin topRestrictedBudget`.

The next continuation pass added the first ordinary padded-forest transport
facts. Embedded top restricted vertices now commute with the padded top parent
map, and every charged top projected path can be lifted to a valid ordinary
`RawCompressionPath` over `Fin topRestrictedBudget` with cost at least the
charged projected-step cost:

```lean
RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode

RawCompressionExecution
  .rankThreshold_topProjected_charged_path_lifts_to_padded_valid_path
```

This path lift appends the top parent of the projected target to meet the
ordinary source-path validity requirement `2 <= P.len.val`. It is therefore a
valid cost-dominating path lift, but not yet a full step-realization theorem.

The latest continuation split off the semantic edge case. A zero-cost top
projected step is now proved to be identity on the top restricted parent map:

```lean
RawCompressionStep.topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero
```

And charged top projected paths with positive cost now lift directly, without
the appended parent, to valid ordinary paths over the padded top budget with
exactly matching cost:

```lean
RawCompressionExecution
  .rankThreshold_topProjected_charged_positive_path_lifts_to_padded_valid_path
```

This removes the earlier ambiguity around whether every charged path must use
the appended-parent construction. The appended lift remains useful for coarse
cost domination; the exact positive-cost lift is the one intended for ordinary
step realization.

The current continuation added the first actual ordinary step realization:

```lean
RawCompressionExecution
  .rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
```

For a positive-cost charged top projected step, this produces a valid
`RawCompressionStep` over `Fin topRestrictedBudget`, with matching source cost
and rank-threshold packing on both the before and after forests.  The proof is
factored through the generic source-model constructor:

```lean
RawCompressionPath.exists_valid_step_of_valid_nonroot_path
```

which builds the standard compressed after-forest for any valid nonroot source
path.  Thus the positive-cost semantic step case is solved locally.  The
ordinary execution is still not assembled, because zero-cost charged slots and
cross-slot exact before/after coordinates still need to be packaged.

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

## First Remaining Obstruction

The charged-subsequence execution construction over `Fin Ct.chargedCount` is
now solved for the dependent projected API.

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

The first remaining obstruction on the direct route is the ordinary padded
source-step construction over:

```lean
RawCompressionExecution
  Ct.chargedCount
  (RankThresholdDissection.topRestrictedBudget (n := n) s)
  (r - s - 1)
```

The remaining sub-obstructions are:

- Path lifting: a valid cost-dominating `RawCompressionPath` over the padded
  top forest is now proved. Positive-cost charged paths also have an exact
  valid lift without appending the projected target's parent. Zero-cost top
  projected steps are proved identity on top parents.
- Semantic validity: positive-cost charged projected paths now produce valid
  ordinary padded source steps with matching cost and before/after
  rank-packing. The remaining semantic work is to package zero-cost charged
  slots as no-ops/skips and align exact consecutive padded coordinates across
  the assembled execution.
- Base accounting: build the legacy injection for the charged top execution,
  not just rank-threshold packing. The existing padding lemmas supply the
  rank-packing part, but not the charge-unit injection.
- Cost domination: prove the charged-only padded execution has cost at least
  `Ct.consumableCost`.
- TopDownCost consumption: apply `RawCompressionExecution.cost_le_topDownCost`
  to the padded valid execution, then feed the result to the new
  `rankThreshold_top_consumableCost_le_JInput_topBudget_of_topDownCost`.

## Viable Strategy

Strategy A remains the clearest mathematical route. The charged-slot projected
API is now in place; the next Strategy A step is to transport each charged
projected step into an ordinary padded source step and assemble those steps
into a `RawCompressionExecution`.

Strategy B is viable once the charged-slot ordinary execution exists, because
the budgeted arithmetic and padded rank-packing side are now available.

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

The charged-subsequence consecutive-state bridge is now proved as:

```lean
theorem rankThresholdTopChargedSlot_after_commutes_with_next

theorem rankThresholdTopChargedProjectedExecution_hasConsecutiveStates
```

and the charged-only projected execution is packaged as:

```lean
noncomputable def rankThresholdTopChargedProjectedExecution
```

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

The padded-parent transport lemma and validity-strengthened path lift are now
proved:

```lean
theorem topRestrictedForestFin_padded_parent_of_topNode

theorem rankThreshold_topProjected_charged_path_lifts_to_padded_valid_path

theorem topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero

theorem rankThreshold_topProjected_charged_positive_path_lifts_to_padded_valid_path

theorem exists_valid_step_of_valid_nonroot_path

theorem rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
```

The smallest next theorem is now a zero-cost/no-op padding theorem, followed
by an assembled execution theorem combining no-op slots with the already
proved positive-cost padded steps:

```lean
theorem rankThreshold_topProjected_charged_zero_cost_lifts_to_padded_noop_step

theorem rankThreshold_topProjected_charged_execution_lifts_to_padded_valid_execution
```

The assembled theorem should be stated so adjacent charged steps can use
`rankThresholdTopChargedProjectedExecution_hasConsecutiveStates` to prove
ordinary `RawCompressionExecution.HasConsecutiveStates`, and it must also
construct the legacy base-accounting injection for the resulting execution.

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

Ambition C-minus/D-plus achieved: the charged-only dependent projected top
execution is constructed, semantically valid in the projected API, and has
cost exactly `Ct.consumableCost`. In addition, charged top projected paths now
lift to valid cost-dominating ordinary paths over the padded top budget;
positive-cost charged paths lift with exact cost, and zero-cost top projected
steps are identity on top parents. Positive-cost charged projected steps now
also realize as valid ordinary padded source steps with before/after
rank-packing. The ordinary padded `RawCompressionExecution` over
`Fin topRestrictedBudget` is still not constructed.
