# Concrete Source Model Failure Report

Branch: `lean-concrete-source-model-v1`

Current status: Ambition B is complete for the base-accounted concrete cost
family.  Ambition A remains open on the concrete shift theorem.

## Summary

The remaining gap cannot be closed honestly by the current finite source-model
skeleton alone.  The current Lean code defines a concrete finite execution
skeleton and proves the base source obligation for executions equipped with an
explicit base-rank-accounting certificate:

```lean
theorem ConcreteSourceModel.topDown_base_bound :
    ConcreteSourceModel.topDownBaseBoundTarget

theorem ConcreteSourceModel.topDown_base_sourceBound :
    SourceBound ConcreteSourceModel.topDownCost 0 (J 0)
```

It also provides conditional wrappers showing that the full downstream
pipeline follows from the single remaining shift theorem:

```lean
def ConcreteSourceModel.topDown_sourceModel_of_shift
    (hshift : forall k : Nat,
      ConcreteSourceModel.topDownShiftStepTarget k) :
    SourceModel

theorem ConcreteSourceModel.sourceRecurrence_topDownCost_of_shift
    (hshift : forall k : Nat,
      ConcreteSourceModel.topDownShiftStepTarget k) :
    SourceRecurrence ConcreteSourceModel.topDownCost

theorem ConcreteSourceModel.paper_finite_bound_topDownCost_of_shift
    (hshift : forall k : Nat,
      ConcreteSourceModel.topDownShiftStepTarget k)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    ConcreteSourceModel.topDownCost m n (L n) <=
      (alphaQ m n + 3) * m + 4 * n
```

However, it does not yet formalize the Seidel--Sharir dissection machinery
needed for the shift theorem:

```lean
def ConcreteSourceModel.topDownShiftStepTarget (k : Nat) : Prop :=
  SourceShiftStep ConcreteSourceModel.topDownCost k (JInput k)
```

Proving this target requires the source main lemma about dissecting a
compression sequence into bottom/top projected sequences and bounding their
costs.  The present Lean objects do not yet include dissections or projected
executions, so a direct proof of `topDownShiftStepTarget` would be missing the
central combinatorial content.

## 1. Current Lean Objects

The current concrete skeleton is in:

```text
formalization/lean/PathCompressionDigestion/ConcreteSourceModel.lean
```

It defines the following finite objects.

- `RawRankedForest n r`

  A parent map and rank map over `Fin n`, with ranks bounded by `r`:

  ```lean
  structure RawRankedForest (n r : Nat) where
    parent : Fin n -> Fin n
    rank : Fin n -> Fin (r + 1)
  ```

- `RawRankedForest.IsRankValid`

  The rank-validity condition that every non-root parent step strictly
  increases rank.

- `RawCompressionPath n`

  A bounded active path with length at most `n + 1`, a node slot array, and a
  target ancestor:

  ```lean
  structure RawCompressionPath (n : Nat) where
    len : Fin (n + 2)
    node : Fin (n + 1) -> Fin n
    target : Fin n
  ```

- `RawCompressionPath.IsRootPath` and `RawCompressionPath.IsNonrootPath`

  Source-style classification by whether the target ancestor is a root.

- `RawCompressionPath.sourceCost`

  Source-style path cost: rootpaths cost zero; nonrootpaths cost the number of
  active vertices strictly before the target.

- `RawCompressionStep n r`

  A before forest, after forest, and path.

- `RawCompressionStep.IsValid`

  A raw step validity predicate: path validity, rank preservation, rootpath
  no-op behavior, nonrootpath rewiring to the old parent of the target, and
  preservation of all other parents.

- `RawCompressionExecution m n r`

  A finite sequence of exactly `m` compression slots.

- `RawCompressionExecution.HasBaseRankAccounting`

  A certificate assigning each charged unit injectively to a vertex and one of
  that vertex's possible parent-rank increases below `r`.

- `RawCompressionExecution.IsValid`

  Valid steps, consecutive before/after states, and the base-rank-accounting
  certificate.

- `ConcreteSourceModel.topDownCost : SourceCostFamily`

  The finite supremum of costs of valid, base-accounted executions.

## 2. Exact Mismatch With `SourceModel`

`SourceModel` requires:

```lean
structure SourceModel where
  Cost : SourceCostFamily
  base_bound : SourceBound Cost 0 (J 0)
  shifting_step : forall k : Nat, SourceShiftStep Cost k (JInput k)
```

The current concrete skeleton supplies the `Cost` and proves the `base_bound`
field for base-accounted executions:

```lean
Cost := ConcreteSourceModel.topDownCost
base_bound := ConcreteSourceModel.topDown_base_bound
```

Thus the original Ambition-B base obligation is now represented directly as a
Lean theorem, not merely as a target Prop.

The missing field is:

```lean
shifting_step :
  forall k : Nat,
    SourceShiftStep ConcreteSourceModel.topDownCost k (JInput k)
```

The mismatch is not a type mismatch.  It is a missing combinatorial theorem.
`SourceShiftStep` is the Seidel--Sharir Lemma 5 shift:

```text
if f(m,n,r) <= k*m + 2*n*g(r),
then f(m,n,r) <= (k+1)*m + 2*n*g^diamond(r).
```

The current `RawCompressionExecution` has no Lean definitions for:

- a rank-threshold dissection `(X_b, X_t)`;
- bottom/top restricted forests;
- projected bottom/top paths for each raw compression path;
- projected bottom/top executions;
- the nonrootpath count `|C|`;
- the main-lemma inequalities
  `|C_b| + |C_t| <= |C|` and
  `Cost(C) <= Cost(C_b) + Cost(C_t) + |X_b| + |C_t|`.

Those are exactly the objects used by the source proof of the shift lemma.

## 3. Does The Source Give Enough Detail?

Yes, at the mathematical level.  The source anchors identify enough structure
to define the missing objects:

- paths from a node to an ancestor;
- rootpath/nonrootpath classification;
- compression of rootpaths and nonrootpaths;
- path cost and sequence cost;
- dissections of ranked forests into bottom/top parts;
- preservation of dissections under path compression;
- the main lemma bounding the cost of a sequence by the costs of its
  bottom/top projections plus the two error terms.

The source details are not yet enough in Lean because the current skeleton
does not encode the dissection/projection API.  That is modeling work, not a
failure of the Ackermann/J hierarchy or source-recurrence bridge.

## 4. Smallest Theorem To Attack Next

The smallest useful theorem is not the full shift lemma.  It is the concrete
main-lemma statement over explicit projected executions:

```lean
-- Proposed next target, after defining dissections and projections.
def RawDissectionMainLemmaTarget : Prop :=
  forall {m n r : Nat}
    (E : RawCompressionExecution m n r)
    (D : RawDissection ...),
    E.RawValid ->
      projectedExecutionsAreValid E D /\
      nonrootCount bottom + nonrootCount top <= nonrootCount E /\
      E.rawCost <= bottom.rawCost + top.rawCost + bottomSize D + nonrootCount top
```

Exact parameters should be filled in after defining `RawDissection`,
restricted forests, and projected paths.

Once this is available, the next theorem is the actual shift target:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

Only after that theorem should Lean define:

```lean
theorem topDown_sourceModel : SourceModel
theorem sourceRecurrence_topDownCost :
    SourceRecurrence topDownCost
```

## 5. Recommended Next Step

The next step should be **model-definition work followed by combinatorial proof
work**.

Do not refactor `SourceModel` yet.  Its API is aligned with the paper-facing
bridge: a base bound plus the Seidel--Sharir shift step imply
`SourceRecurrence`.

Recommended sequence:

1. Split `RawCompressionExecution.IsValid` into raw validity and accounting
   validity:

   ```lean
   def RawCompressionExecution.RawValid ...
   theorem rawValid_hasBaseRankAccounting ...
   ```

2. Define rank-threshold dissections and projected paths/executions.

3. Prove the source main lemma over those projected executions.

4. Prove `topDownShiftStepTarget`.

5. Package `topDown_sourceModel` and derive `sourceRecurrence_topDownCost`.

Until step 4 is complete, there is no honest unconditional paper-facing finite
theorem for `topDownCost`.
