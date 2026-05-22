# Source Recurrence Model Status

Branch: `lean-source-recurrence-model-v1`

Follow-on branch: `lean-concrete-source-model-v1`

Starting checkpoint after fetching `origin/main`:
`a742bb89c768645ae17943604c578693b3cad94a`

## Achieved in this branch

This branch adds a non-opaque iteration bridge from source-style base and
shifting obligations to the existing `SourceRecurrence` interface.

New Lean modules:

- `PathCompressionDigestion/SourceIteration.lean`
- `PathCompressionDigestion/SourceModel.lean`

The core theorem is:

```lean
theorem sourceRecurrence_of_iterated_shifting
    {F : SourceCostFamily}
    (hbase : SourceBound F 0 (J 0))
    (hshift : forall k : Nat, SourceShiftStep F k (JInput k)) :
    SourceRecurrence F
```

The proof is by induction on `k`, using the existing concrete `J` hierarchy
and the fact that `J (k + 1)` is the diamond transform of `J k`.

The structured wrapper theorem is:

```lean
theorem sourceRecurrence_of_shifting
    (M : SourceModel) :
    SourceRecurrence M.Cost
```

The paper-facing finite bound is also available for any such structured source
model:

```lean
theorem paper_finite_bound_of_source_model
    (M : SourceModel)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    M.Cost m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

The existing conditional theorem
`paper_finite_bound_of_source_recurrence` remains unchanged.

## Follow-on concrete skeleton

The follow-on branch `lean-concrete-source-model-v1` adds:

- `PathCompressionDigestion/ConcreteSourceModel.lean`

This module defines finite raw objects for:

- ranked forests over `Fin n`, with parent pointers and ranks bounded by `r`;
- roots, leaves, ancestors, and the rank-validity discipline;
- bounded top-down compression paths;
- single compression steps that preserve ranks and rewire nonrootpath vertices
  to the old parent of the path target;
- finite compression executions, source-style rootpath/nonrootpath cost, and
  base-case rank-accounting certificates;
- `topDownCost : SourceCostFamily`, defined as the finite supremum of valid
  base-accounted execution costs in this skeleton.

It proves the source base obligation for that base-accounted concrete cost:

```lean
theorem topDown_base_bound :
    topDownBaseBoundTarget

theorem topDown_base_sourceBound :
    SourceBound topDownCost 0 (J 0)
```

It also records the remaining shift proof target as a `Prop` definition, not
an assumption:

```lean
def topDownBaseBoundTarget : Prop :=
  SourceBound topDownCost 0 (J 0)

def topDownShiftStepTarget (k : Nat) : Prop :=
  SourceShiftStep topDownCost k (JInput k)

def topDownSourceModelTarget : Prop :=
  topDownBaseBoundTarget /\ forall k : Nat, topDownShiftStepTarget k
```

The shift target is not proved in the follow-on branch.

Because the base field is now proved, the module also provides conditional
wrappers showing that the only missing ingredient for the full source-model
pipeline is the concrete shift theorem:

```lean
def topDown_sourceModel_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceModel

theorem sourceRecurrence_topDownCost_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceRecurrence topDownCost

theorem paper_finite_bound_topDownCost_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    topDownCost m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

## Not achieved

The bridge branch does not define a concrete top-down path-compression
execution model and does not prove Seidel--Sharir Lemma 5 from such a model.
The follow-on concrete skeleton defines finite execution objects and
`topDownCost`, and proves the base bound for executions equipped with the
base-rank-accounting certificate. It still does not derive that certificate
from the raw step semantics, and it does not prove the Seidel--Sharir shift
obligation for that cost family.

No unconditional theorem of the following form exists yet:

```lean
theorem sourceRecurrence_of_topDownModel :
    SourceRecurrence topDownCost
```

and therefore no unconditional finite theorem for `topDownCost` exists yet.

## Remaining exact gap

1. Source-model definition now has a first finite skeleton, but its exact
   match to the source cost functional `f(m,n,r)` still needs audit against
   Seidel--Sharir's path-compression model.
2. Missing certificate theorem: a proof that every raw source-valid compression
   execution admits the base-rank-accounting certificate used by
   `topDownCost`.
3. Missing combinatorial shifting content: a proof that any bound
   `f(m,n,r) <= k*m + 2*n*g(r)` for a valid source row `g` implies
   `f(m,n,r) <= (k+1)*m + 2*n*g^diamond(r)`.
4. Blocker type: combinatorial proof work plus source-model audit, not a
   failure of the existing `J`/Ackermann comparison lane.
5. Smallest next theorem: prove that raw valid compression executions produce
   the base-rank-accounting certificate, then attack
   `topDownShiftStepTarget`.
