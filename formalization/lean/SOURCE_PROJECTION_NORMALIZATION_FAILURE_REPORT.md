# Source Projection Normalization Failure Report

Branch: `lean-source-projection-normalization-v1`

Starting point used locally: `7c541db3481d693ab0ff4beb20f423941d6e59f4`

Note: after `git fetch origin`, `origin/main` was
`fb2ab21be33d2ddb658e1f324ecd6a2dd8413f1a` and did not contain
`7c541db3481d693ab0ff4beb20f423941d6e59f4` as an ancestor.  The new branch was
therefore created at `7c541db3481d693ab0ff4beb20f423941d6e59f4`, the prior
source-projection worker tip that supplies `SourceProjection.lean`.

## Summary

The current projected execution layer cannot yet be turned into an ordinary
`RawCompressionExecution` accepted by `RawCompressionExecution.IsValid` without
adding a real normalization/materialization API.  The mismatch is structural,
not a local rewriting problem.

The existing projected facts are useful and should be preserved:

```lean
RawCompressionPath.ProjectedCompressionExecution
RawCompressionPath.ProjectedCompressionExecution.HasConsecutiveStates
RawCompressionExecution.rankThresholdTopProjectedExecution_hasConsecutiveStates
RawCompressionExecution.rankThresholdBottomProjectedExecution_hasConsecutiveStates
RawCompressionExecution.cost_le_canonicalProjectedExecutions_cost_add_topNonrootCount
RawCompressionExecution.canonicalProjectedExecutions_nonrootCount_add_le_nonrootCount
```

However, these theorems only assemble dependent projected steps whose adjacent
states commute up to explicit equivalences.  They do not produce ordinary
source executions in the current concrete model.

## 1. Exact Current Type Mismatch

The projected execution type in `SourceProjection.lean` is:

```lean
structure RawCompressionPath.ProjectedCompressionExecution (m : Nat) where
  vertex : Fin m -> Type*
  step : forall i : Fin m, ProjectedCompressionStep (vertex i)
```

Each projected step contains only:

```lean
structure RawCompressionPath.ProjectedCompressionStep (alpha : Type*) where
  beforeParent : alpha -> alpha
  afterParent : alpha -> alpha
  path : ProjectedPathSegment alpha beforeParent
```

and consecutive projected slots are connected only by:

```lean
def ProjectedCompressionExecution.HasConsecutiveStates (E : ProjectedCompressionExecution m) : Prop :=
  forall i j : Fin m, i.val + 1 = j.val ->
    Exists fun e : Equiv (E.vertex i) (E.vertex j) =>
      (E.step i).ParentCommutesWithEquiv (E.step j) e
```

By contrast, an ordinary concrete source execution in
`ConcreteSourceModel.lean` is:

```lean
structure RawCompressionExecution (m n r : Nat) where
  step : Fin m -> RawCompressionStep n r
```

with validity:

```lean
def RawCompressionExecution.IsValid (E : RawCompressionExecution m n r) : Prop :=
  (forall i : Fin m, (E.step i).IsValid) /\
    (forall i j : Fin m,
      i.val + 1 = j.val -> (E.step i).after = (E.step j).before) /\
    E.HasBaseRankAccounting
```

The mismatches are:

1. `ProjectedCompressionExecution.vertex` is dependent in `i`; ordinary
   executions use one fixed universe `Fin n`.
2. Projected consecutive states commute through explicit equivalences;
   ordinary consecutive states require literal equality of `RawRankedForest`
   values.
3. Projected steps carry parent maps and a parent-chain segment, but no
   `RawRankedForest` ranks, no rank-bound data, no rank-preservation theorem,
   and no after-forest value.
4. `ProjectedPathSegment.len : Nat` may be `0` or `1`; ordinary
   `RawCompressionPath.IsValidFor` requires `2 <= P.len.val`.
5. Projected path cost is `edgeCost = len - 1`; ordinary source cost is
   `sourceCost`, which is zero for rootpaths and `P.cost` for nonrootpaths.
   A one-vertex projected top segment can be nonroot-like with projected cost
   `0`, which has no exact ordinary valid source-step representation under the
   current `RawCompressionPath` API.
6. `RawCompressionExecution.IsValid` bundles `HasBaseRankAccounting`.
   The projected execution layer has no charge injection and the current raw
   cost inequalities do not provide one.

Because of item 6, even a successful semantic materialization would still not
be usable by `topDownCost` unless it also produced `HasBaseRankAccounting` or
the cost family API were split.

## 2. Recommended Solution Shape

The right next step is materialization, not quotienting alone.

A quotient/reindexing theorem can remove the explicit equivalences between
adjacent projected states, but it still leaves parent-only steps without ranks,
valid raw paths, rewiring semantics, or base accounting.  The normal form
needed by the current concrete API should instead choose canonical
representatives and build ordinary forests.

Two viable materialization routes:

1. Same-universe materialization over `Fin n`.
   Define bottom/top restricted forests on the original vertex universe,
   making vertices outside the selected side fixed roots.  This avoids proving
   that projected path length is bounded by the side cardinal.

2. Packed-side materialization over `Fin D.bottomFinset.card` and
   `Fin D.topFinset.card`.
   This is closer to the paper's restricted-subproblem sizes, but it needs
   additional no-duplicate/path-length lemmas to fit projected paths into
   `RawCompressionPath` over the packed side cardinal.

The same-universe route is the smallest mechanically plausible route.  It can
prove semantic validity first, then later add side-cardinality packing if the
recurrence proof needs the exact `|X_b|` and `|X_t|` parameters.

## 3. Smallest Theorem That Would Unblock The Main Lemma

The current `RawCompressionExecution.IsValid` is too strong for the first
normalization theorem because it includes base-rank accounting.  The smallest
useful API split is:

```lean
def RawCompressionExecution.IsSemanticallyValid
    (E : RawCompressionExecution m n r) : Prop :=
  (forall i : Fin m, (E.step i).IsValid) /\
    (forall i j : Fin m,
      i.val + 1 = j.val -> (E.step i).after = (E.step j).before)
```

Then the smallest bottom theorem should be:

```lean
theorem rankThresholdBottomProjectedExecution_materializes_semantically
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Exists fun Eb : RawCompressionExecution m n s =>
      Eb.IsSemanticallyValid /\
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).cost <= Eb.cost /\
      Eb.nonrootCount <=
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).nonrootCount
```

The top theorem should be symmetric, with the top rank bound chosen from the
existing shifted-rank facts, for example `r - (s + 1)` if the materialized
forest uses shifted top ranks.

To unblock the current `topDownCost` recurrence API without refactoring, the
stronger theorem would also need:

```lean
Eb.HasBaseRankAccounting
```

and similarly for the top execution.  No existing projected-execution theorem
contains enough information to derive that certificate.  This is the main
reason the normalization layer is blocked against the current cost-family API.

## 4. ConcreteSourceModel Rigidity

Several definitions in `ConcreteSourceModel.lean` are too rigid for immediate
projected-execution normalization:

1. `RawCompressionPath.IsValidFor` requires `2 <= P.len.val`.  Projected
   restricted segments naturally include empty and one-vertex side projections.
   Bottom one-vertex projections are root-like in the current cut model, but
   top one-vertex projections can be nonroot-like with projected cost `0`.

2. `RawCompressionExecution.IsValid` bundles semantic validity with
   `HasBaseRankAccounting`.  This prevents using ordinary semantic restricted
   executions as intermediate objects in the shift proof.

3. `RawCompressionExecution` is fixed to `Fin n`.  This is workable for
   same-universe materialization, but awkward for paper-faithful packed
   restricted subproblems over `|X_b|` and `|X_t|`.

4. `RawCompressionStep.IsValid` requires exact concrete rewiring semantics.
   The projected step API currently records parent maps and parent-chain
   paths, but it does not package the theorem that projected after-parents
   satisfy the ordinary nonrootpath rewiring rule after materialization.

## Recommended Next Worker Target

Do not start by proving `topDown_shift_step`.  First split semantic execution
validity from base accounting and prove same-universe semantic
materialization for the bottom projection:

```lean
RawDissection.bottomRestrictedForestOnFin
RawCompressionPath.ProjectedPathSegment.toRawPathOnFin
RawCompressionStep.bottomProjectedStep_materializes
RawCompressionExecution.rankThresholdBottomProjectedExecution_materializes_semantically
```

Then repeat for top, resolving the one-vertex top nonroot segment by either:

1. allowing projected/no-op source slots in a separate restricted execution
   API; or
2. proving an inequality-form materialization where normalized top cost may be
   larger than projected cost and the boundary term absorbs the extra unit.

Only after that should a worker connect the materialized executions to
`topDownCost`; that connection needs either base-accounting certificates for
the materialized executions or an API refactor that keeps base accounting out
of the cost family used by the shift recurrence.

## Current Verdict

Ambition D achieved.  The exact blocker is identified.  Projected executions
do not yet normalize to ordinary valid restricted executions in the current
API, and the source dissection main lemma remains unproved.
