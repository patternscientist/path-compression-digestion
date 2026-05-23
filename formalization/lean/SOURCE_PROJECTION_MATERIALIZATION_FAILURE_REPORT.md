# Source Projection Materialization Failure Report

Branch: `lean-source-projection-materialization-v1`

Starting commit: `d42aee408271aa23f274d35753c6d5f7b043eda4`

## Summary

The previous API split succeeded: ordinary concrete executions now expose
semantic validity separately from base/rank accounting, and dependent projected
executions expose projected semantic validity.  That split is necessary, but it
is not yet sufficient to materialize bottom/top projected executions as
ordinary `RawCompressionExecution`s.

The current obstruction is not merely that adjacent projected slots are linked
by equivalences.  Even after choosing representatives on a fixed universe, a
projected step carries only parent maps and a projected parent-chain segment,
whereas `RawCompressionStep.IsValid` requires a specific top-down compression
rewrite for a `RawCompressionPath` of length at least two.

## 1. Exact Projected Type Being Materialized

The projected execution type is:

```lean
RawCompressionPath.ProjectedCompressionExecution m
```

with fields:

```lean
vertex : Fin m -> Type*
step : forall i : Fin m, ProjectedCompressionStep (vertex i)
```

For a raw execution `E`, the bottom projection is:

```lean
E.bottomProjectedExecution hsteps D cut hcut
```

where:

```lean
vertex i = (D i).BottomNode
step i = (E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)
```

The top projection is:

```lean
E.topProjectedExecution hsteps D cut hcut
```

where:

```lean
vertex i = (D i).TopNode
step i = (E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)
```

Each projected step has the parent-map-only shape:

```lean
structure RawCompressionPath.ProjectedCompressionStep (alpha : Type*) where
  beforeParent : alpha -> alpha
  afterParent : alpha -> alpha
  path : ProjectedPathSegment alpha beforeParent
```

The available semantic theorem is:

```lean
ProjectedCompressionExecution.IsSemanticallyValid
```

which is definitionally the existing consecutive-state condition up to
explicit equivalences:

```lean
ProjectedCompressionExecution.HasConsecutiveStates
```

## 2. Exact Ordinary Target Type

The ordinary target is a concrete source execution:

```lean
RawCompressionExecution m n r
```

with semantic validity:

```lean
RawCompressionExecution.IsSemanticallyValid
```

Expanding the definitions, this requires:

```lean
RawCompressionExecution.HasValidSteps E /\
RawCompressionExecution.HasConsecutiveStates E
```

In particular, every materialized slot must be an ordinary
`RawCompressionStep n r` satisfying:

```lean
RawCompressionStep.IsValid
```

which includes:

```lean
S.path.IsValidFor S.before
S.after.IsRankValid
forall v, S.after.rank v = S.before.rank v
S.path.IsRootPath S.before -> S.after.parent = S.before.parent
S.path.IsNonrootPath S.before ->
  forall v, S.path.IsCompressedVertex v ->
    S.after.parent v = S.before.parent S.path.target
forall v, Not (S.path.IsCompressedVertex v) ->
  S.after.parent v = S.before.parent v
```

If the materialized execution must be directly consumable by `topDownCost`,
the target is stronger:

```lean
RawCompressionExecution.IsValid
```

which is now factored as:

```lean
E.IsSemanticallyValid /\ E.HasBaseRankAccounting
```

## 3. First Obstruction

The first obstruction for direct materialization is the mismatch between
projected parent-map evolution and `RawCompressionStep.IsValid` rewiring
semantics.

Consider the bottom projection of a valid raw step whose dissection cut has a
nonempty top suffix:

```lean
cut < S.path.len.val
```

The existing theorem proves:

```lean
RawCompressionPath.bottomProjectionSegment_isRootPath_of_top_nonempty
```

So the bottom projected path is root-like in the restricted bottom parent map.
If this projected step were converted directly into an ordinary
`RawCompressionStep`, `RawCompressionStep.IsValid` would put it in the
rootpath branch and require:

```lean
after.parent = before.parent
```

But the projected bottom after-parent is:

```lean
S.afterBottomParent D hS
```

For an original nonroot compression step, compressed bottom vertices may be
rewired by the raw step to the old parent of the original path target, which
lies in the top side.  The restricted bottom after-parent then truncates that
top edge to a self-loop, while the restricted bottom before-parent still
follows the bottom prefix.  Thus the projected bottom after-parent need not
equal the projected bottom before-parent even though the projected bottom path
is root-like.

This is not fixable by quotienting the adjacent vertex types.  Quotienting can
address the equivalence-linked consecutive states, but it does not turn this
parent-map evolution into the concrete source rewrite required by
`RawCompressionStep.IsValid`.

There are additional obstructions after that first one:

1. `ProjectedPathSegment.len : Nat` may be `0` or `1`, while
   `RawCompressionPath.IsValidFor` requires `2 <= P.len.val`.
2. A projected step has no rank field.  Any materialized `RawRankedForest`
   must choose ranks and prove `IsRankValid` for both before and after
   forests.
3. A packed-side materialization over `Fin side.card` needs a reindexing
   theorem plus path-length/no-duplicate control.  A same-universe
   materialization over `Fin n` avoids the cardinality issue but still faces
   the rootpath/rewiring mismatch above.
4. `topDownCost` still ranges over executions satisfying
   `HasBaseRankAccounting`.  The projected execution API contains no charge
   injection, so semantic materialization alone is not enough for direct
   consumption by `topDownCost`.

## 4. Smallest Next Theorem To Unblock Materialization

The smallest useful next definition is not a full ordinary
`RawCompressionExecution`; it is a relaxed restricted-step semantic that
matches the projection output:

```lean
def ProjectedCompressionStep.RealizesRestrictedRewrite
    (S : ProjectedCompressionStep alpha) : Prop := ...
```

or, equivalently, a new ordinary-step predicate that allows zero/one-length
projected slots and restricted-edge truncation:

```lean
def RawCompressionStep.IsRestrictedProjectionStep
    (S : RawCompressionStep n r) : Prop := ...
```

The smallest theorem after introducing that predicate should be:

```lean
theorem bottomProjectedStep_realizesRestrictedRewrite :
    (S.bottomProjectedStep D hS cut hcut).RealizesRestrictedRewrite

theorem topProjectedStep_realizesRestrictedRewrite :
    (S.topProjectedStep D hS cut hcut).RealizesRestrictedRewrite
```

Then the execution-level bridge should target a restricted-projection
execution first:

```lean
theorem bottomProjectedExecution_materializes_asRestrictedProjectionExecution :
    ...

theorem topProjectedExecution_materializes_asRestrictedProjectionExecution :
    ...
```

Only after that should a worker prove a padding/simulation theorem from
restricted-projection executions into ordinary source executions, with explicit
inequalities:

```lean
projectedCost <= simulated.cost
simulated.nonrootCount <= projected.nonrootCount + boundaryTerm
```

For direct recurrence use through `topDownCost`, the simulation theorem must
also construct:

```lean
simulated.HasBaseRankAccounting
```

or the source-cost family must be refactored so the shift argument consumes
semantic executions first and adds base accounting only where the base bound is
proved.

## Current Verdict

Ambition D achieved.  Bottom and top projected executions do not yet
materialize as ordinary `RawCompressionExecution`s.  The blocking issue is
semantic: projected restricted rewrites are not the same as ordinary
`RawCompressionStep.IsValid` rewrites, even after the previous validity split.
