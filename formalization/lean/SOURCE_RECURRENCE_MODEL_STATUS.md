# Source Recurrence Model Status

Branch: `lean-source-recurrence-model-v1`

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

## Not achieved

This branch does not define a concrete top-down path-compression execution
model and does not prove Seidel--Sharir Lemma 5 from such a model.

No unconditional theorem of the following form exists yet:

```lean
theorem sourceRecurrence_of_topDownModel :
    SourceRecurrence topDownCost
```

and therefore no unconditional finite theorem for an actual `topDownCost`
exists yet.

## Remaining exact gap

1. Missing source-model definition: a Lean representation of the ranked forest,
   path-compression operations, and the cost functional `f(m,n,r)` used by the
   top-down Seidel--Sharir analysis.
2. Missing base case: a proof that the modeled cost satisfies
   `SourceBound topDownCost 0 (J 0)`, or the source-faithful adjusted base row
   if the source recurrence starts from a different indexing convention.
3. Missing combinatorial shifting content: a proof that any bound
   `f(m,n,r) <= k*m + 2*n*g(r)` for a valid source row `g` implies
   `f(m,n,r) <= (k+1)*m + 2*n*g^diamond(r)`.
4. Blocker type: mathematical/modeling ambiguity plus substantial Lean
   engineering, not a failure of the existing `J`/Ackermann comparison lane.
5. Smallest next theorem: instantiate `SourceModel` for a concrete
   top-down path-compression model by proving its `base_bound` and
   `shifting_step` fields.
