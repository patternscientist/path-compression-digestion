# Projected Cost TopDown Domination Failure Report

Branch: `lean-projected-cost-topdown-domination-v1`

Starting base:

```text
origin/main = c7ddbea94941c7f363e4cf9d9166044c66d314e1
merged prerequisite = f19a7cbc7bcec1b29f0d92edcf1d91f2f36788da
```

## Summary

This worker did not prove projected-cost domination by `topDownCost`, and did
not prove:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

The obstruction is sharper than the earlier materialization report: a blanket
domination theorem from the current projected admissibility predicate to
`topDownCost` is false, and the mismatch is not merely the rank-zero base
case.  The current projected admissibility predicate only records
consecutive-state compatibility up to equivalence.  It does not carry the
ordinary source-step rewrite semantics, path-validity lower bound,
rank-validity data, side cardinality, or `HasBaseRankAccounting` certificate
needed by `topDownCost`.

## Mechanical Progress

This branch adds the rank-zero extremal-cost lemma:

```lean
theorem ConcreteSourceModel.topDownCost_rank_zero_eq_zero
    (m n : Nat) :
    topDownCost m n 0 = 0
```

It also adds a projected-admissibility counterexample:

```lean
theorem RawCompressionPath.ProjectedCompressionExecution.exists_admissible_projectedCost_gt_topDownCost_rank_zero :
    Exists fun E : ProjectedCompressionExecution.{0} 1 =>
      E.IsAdmissible /\ E.projectedCost = 1 /\ topDownCost 1 1 0 = 0
```

Continuing from that counterexample, this branch also proves that ordinary
one-vertex raw source steps and executions have zero cost:

```lean
theorem RawCompressionStep.cost_eq_zero_of_one_vertex
    (S : RawCompressionStep 1 r) :
    S.cost = 0

theorem RawCompressionExecution.cost_eq_zero_of_one_vertex
    (E : RawCompressionExecution m 1 r) :
    E.cost = 0

theorem RawCompressionExecution.topDownCost_one_vertex_eq_zero
    (m r : Nat) :
    topDownCost m 1 r = 0
```

Thus the same one-slot projected witness remains above ordinary
one-vertex `topDownCost` at every rank bound:

```lean
theorem RawCompressionPath.ProjectedCompressionExecution.exists_admissible_projectedCost_gt_topDownCost_one_vertex
    (r : Nat) :
    Exists fun E : RawCompressionPath.ProjectedCompressionExecution.{0} 1 =>
      E.IsAdmissible /\ E.projectedCost = 1 /\ topDownCost 1 1 r = 0
```

This proves that the strategy

```lean
E.IsAdmissible -> E.projectedCost <= topDownCost m n r
```

cannot be sound for the current `ProjectedCompressionExecution.IsAdmissible`
predicate.

## Exact Projected-Cost Terms Still Needing Bounds

For rank-threshold recurrence consumption, the remaining projected terms are:

```lean
(E.canonicalBottomProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).projectedCost
```

and

```lean
(E.canonicalTopProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).projectedCost
```

The already-proved theorem

```lean
RawCompressionExecution.rankThreshold_projected_cost_main_lemma_add_length
```

has reduced the accounting side to:

```lean
E.cost <= Cb.projectedCost + Ct.projectedCost + |X_b| + m
```

where `|X_b|` is represented by

```lean
((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

using the proved equality
`rankThreshold_bottomBoundaryCard_eq_bottomFinset_card`.

## Intended `topDownCost` Targets

The natural current-API bottom target would be:

```lean
(E.canonicalBottomProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).projectedCost <=
  topDownCost m
    ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
    s
```

The natural current-API top target would be:

```lean
(E.canonicalTopProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).projectedCost <=
  topDownCost m
    ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card)
    (r - s - 1)
```

These are not enough by themselves for the sharp recurrence arithmetic if both
use the full original `m`; later recurrence consumption may require compacted
operation counts or a separate theorem showing how the projected top/bottom
slot counts combine.  However, even these weaker current-API domination
targets are not presently provable because no simulation into valid
base-accounted ordinary executions exists.

## Blocker Classification

1. Simulation: primary blocker.  Projected steps are restricted parent-map
   rewrites, not ordinary `RawCompressionStep.IsValid` rewrites.
2. Path validity: projected segments may have length `0` or `1`, while
   ordinary source paths require `2 <= P.len.val`.
3. Rank/base accounting: projected executions contain no ranks and no
   `HasBaseRankAccounting` certificate, while `topDownCost` ranges over
   base-accounted ordinary executions.
4. Parameter bookkeeping: side cardinalities and shifted ranks are now mostly
   exposed, but there is no packed or same-universe simulation theorem tying
   those parameters to an ordinary execution.
5. Arithmetic: not the first blocker.  The current failure occurs before the
   final source-shift arithmetic.

## Is `topDownCost` Too Narrow?

Yes for projected admissible executions as currently defined.

The Lean theorem

```lean
RawCompressionPath.ProjectedCompressionExecution.exists_admissible_projectedCost_gt_topDownCost_rank_zero
```

exhibits an admissible one-slot projected execution with projected cost `1`
while `topDownCost 1 1 0 = 0`.  The follow-up theorem

```lean
RawCompressionPath.ProjectedCompressionExecution.exists_admissible_projectedCost_gt_topDownCost_one_vertex
```

shows the same phenomenon for `topDownCost 1 1 r` at every rank bound `r`.
This does not refute a future theorem for the special canonical rank-threshold
projections, but it does refute the broad projected-admissible domination
strategy.

For the rank-threshold projections, `topDownCost` is still too narrow unless a
simulation theorem supplies ordinary valid executions together with
`HasBaseRankAccounting`, or unless the cost family is refactored to range over
a source-correct restricted-projection semantics.

## Smallest Theorem Needed Next

The next theorem should introduce a restricted-projection simulation layer,
not identify projected executions with ordinary executions.  A minimal useful
bottom theorem would have the form:

```lean
theorem rankThresholdBottomProjectedExecution_simulates_to_validExecution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    Exists fun Eb : RawCompressionExecution m
        ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
        s =>
      Eb.IsValid /\
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).projectedCost <= Eb.cost
```

The corresponding top theorem would use the stable top side cardinality and
rank bound `r - s - 1`.

If constructing `Eb.IsValid` is too strong, the next honest API is a new
restricted-projection cost family whose validity predicate matches projected
rewrites, followed by a separately proved simulation or comparison theorem to
ordinary `topDownCost`.

## Verdict

Ambition D achieved.  The broad projected-admissible domination strategy is
mechanically refuted.  The remaining viable route is a sound
restricted-projection simulation/comparison theorem for the canonical
rank-threshold projected executions.
