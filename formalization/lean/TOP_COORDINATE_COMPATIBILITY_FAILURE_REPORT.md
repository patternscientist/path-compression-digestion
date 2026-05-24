# Top Coordinate Compatibility Failure Report

Branch: `lean-top-coordinate-compatibility-v1`

Starting base:

```text
HEAD = 26d4b10f578664fd479fbc86aa756a45f59bcce0
contains = 7b371e0be724a20b7ef1100611694971101ca6bc
contains = e60c205a49e8066347a3ea44837aa1af0e77cae0
contains = 79210d297513b2bea6ea0cf93db0d492f86a1152
```

## Summary

This worker did not prove the requested coordinate-compatibility or lifted
compressed-vertex bridge APIs.

The key new diagnosis is sharper than the previous transition-equality report:
the current coordinate map is not the deterministic ordered enumeration
`Finset.orderEmbOfFin`.  It is built through `Finset.equivFin`, ultimately a
noncomputable `Fintype.equivFin` choice for the subtype of top vertices.
Consequently, pointwise coordinate compatibility across two propositionally
equal top predicates is not available by definitional reduction or by simple
rewriting of the displayed top finset.

## 1. Exact Definition Of `topNodeEquivFin`

The current definition is in `SourceProjection.lean`:

```lean
def RawDissection.topNodeEquivTopFinset
    (D : RawDissection F) :
    Equiv D.TopNode D.topFinset := {
  toFun := fun v => { val := v.1, property := (D.mem_topFinset v.1).2 v.2 },
  invFun := fun v => { val := v.1, property := (D.mem_topFinset v.1).1 v.2 },
  ...
}

noncomputable def RawDissection.topNodeEquivFin
    (D : RawDissection F) :
    Equiv D.TopNode (Fin D.topFinset.card) := by
  classical
  exact D.topNodeEquivTopFinset.trans D.topFinset.equivFin
```

Thus the concrete coordinate map used by

```lean
RankThresholdDissection.topRestrictedForestFin
```

is:

```lean
let D := dissection F hF s
let e := D.topNodeEquivFin
```

and the restricted parent/rank functions are defined in these coordinates.

## 2. What `topNodeEquivFin` Depends On

Top-node membership itself depends only on the top predicate, and for
rank-threshold dissections this depends only on `rankNat`:

```lean
(RankThresholdDissection.dissection F hF s).IsTop v <-> s < F.rankNat v
```

However, the coordinate enumeration also depends on:

```lean
D.topFinset.equivFin
```

This is not the order-preserving `Finset.orderEmbOfFin` enumeration.  It is a
noncomputable finite-type equivalence for the subtype `D.topFinset`.  Even when
two top predicates have extensionally equal top finsets, the two subtype
expressions and their `Fintype.equivFin` choices are not definitionally the
same in the places needed by the padded after-state proof.

The attempted generic theorem:

```lean
theorem RawDissection.topNodeEquivFin_val_eq_of_topFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.topFinset = D'.topFinset)
    (x : Fin n)
    (hx : D.IsTop x)
    (hx' : D'.IsTop x) :
    (D.topNodeEquivFin { val := x, property := hx }).val =
      (D'.topNodeEquivFin { val := x, property := hx' }).val
```

blocked when eliminating or rewriting `hset`: the goal contains dependent
membership proofs inside the subtype arguments to `equivFin`, and the rewrite
motive is not type-correct.  This is evidence that the current coordinate API
is not designed for transport across propositionally equal top predicates.

## 3. Exact Coordinate Compatibility Theorem Needed

If the current `topNodeEquivFin` coordinate system is preserved, the needed
theorem is the pointwise value compatibility:

```lean
theorem RankThresholdDissection.topNodeEquivFin_val_eq_of_rankNat_eq
    {n r : Nat}
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (x : Fin n)
    (hxF : (RankThresholdDissection.dissection F hF s).IsTop x)
    (hxG : (RankThresholdDissection.dissection G hG s).IsTop x) :
    ((RankThresholdDissection.dissection F hF s).topNodeEquivFin
      { val := x, property := hxF }).val =
    ((RankThresholdDissection.dissection G hG s).topNodeEquivFin
      { val := x, property := hxG }).val
```

For after-state equality, an inverse-coordinate form is also likely needed:

```lean
theorem RankThresholdDissection.topNodeEquivFin_symm_val_eq_of_rankNat_eq
    {n r : Nat}
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (hcard :
      (RankThresholdDissection.dissection F hF s).topFinset.card =
      (RankThresholdDissection.dissection G hG s).topFinset.card)
    (a : Fin (RankThresholdDissection.dissection F hF s).topFinset.card) :
    (((RankThresholdDissection.dissection F hF s).topNodeEquivFin).symm a).1 =
    (((RankThresholdDissection.dissection G hG s).topNodeEquivFin).symm
      (Fin.cast hcard a)).1
```

The present codebase does not provide either theorem.

## 4. Exact Compressed-Vertex Definition In The Lifted Padded Path

The ordinary source compressed-vertex predicate is:

```lean
def RawCompressionPath.IsCompressedVertex
    (P : RawCompressionPath n) (v : Fin n) : Prop :=
  exists i : Fin (n + 1), i.val + 1 < P.len.val /\ P.node i = v
```

The positive top-step lift constructs a local padded path inside:

```lean
RawCompressionExecution
  .rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
```

with the shape:

```lean
let N := RankThresholdDissection.topRestrictedBudget (n := n) s
let D := E.rankThresholdDissectionFamily hE.1 s i
let seg := (E.step i).path.topProjectionSegment D ...
let e := D.topNodeEquivFin
let embed : D.TopNode -> Fin N := fun v =>
  { val := (e v).val, isLt := (e v).isLt.trans_le hcard_le_budget }
let last : Fin seg.len := seg.lastIndex hseg_pos
let targetNode : Fin N := embed (seg.node last)
let P : RawCompressionPath N := {
  len := { val := seg.len, isLt := by omega }
  node := fun j =>
    if hj : j.val < seg.len then embed (seg.node { val := j.val, isLt := hj })
    else targetNode
  target := targetNode
}
```

This `P` is not currently factored out as a named definition, so downstream
proofs cannot state or reuse a clean compressed-vertex transport theorem.

## 5. Exact Compressed-Vertex Transport Needed

After factoring the lifted path into a reusable definition, the needed theorem
is:

```lean
theorem RawCompressionExecution
    .rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost)
    (v : Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)) :
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged hpos)
        .IsCompressedVertex v <->
      Exists fun a :
        Fin
          ((E.step i).path.topProjectionLength
            (E.rankThresholdDissectionFamily hE.1 s i)
            (E.dissectionCut hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)) =>
        a.val + 1 <
          ((E.step i).path.topProjectionLength
            (E.rankThresholdDissectionFamily hE.1 s i)
            (E.dissectionCut hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)) /\
        v =
          -- the same `embed (seg.node a)` coordinate used in the path
          ...
```

For proving after-parent equality, a one-way introduction theorem may be
enough:

```lean
theorem RawCompressionExecution
    .rankThresholdTopProjectedPaddedPath_isCompressedVertex_of_lt_last
    ...
```

and a corresponding elimination theorem for non-compressed padded vertices.

## 6. Smallest Next Theorem Statement

The smallest next theorem should avoid the current arbitrary `equivFin`
transport problem by introducing deterministic top coordinates.  The clean
route is:

```lean
noncomputable def RawDissection.topNodeOrderEquivFin
    (D : RawDissection F) :
    Equiv D.TopNode (Fin D.topFinset.card)
```

implemented through `D.topFinset.orderEmbOfFin` and its inverse/range theorem,
or an equivalent order-isomorphism already available in Mathlib.  Then prove:

```lean
theorem RawDissection.topNodeOrderEquivFin_val_eq_of_topFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.topFinset = D'.topFinset)
    (x : Fin n)
    (hx : D.IsTop x)
    (hx' : D'.IsTop x) :
    (D.topNodeOrderEquivFin { val := x, property := hx }).val =
      (D'.topNodeOrderEquivFin { val := x, property := hx' }).val
```

After that, either:

1. redefine `topRestrictedForestFin` and the padded lift to use the deterministic
   ordered coordinate equivalence, or
2. prove that the existing `topNodeEquivFin` agrees with the deterministic
   ordered equivalence in the cases used by `topRestrictedForestFin`.

Option 1 is probably the smaller long-term API repair, but it changes a core
coordinate definition and should be done as a dedicated refactor with all
existing lemmas rebuilt.

## Verdict

Ambition D achieved.  The coordinate compatibility theorem is blocked by the
current noncanonical `topNodeEquivFin` definition, and the compressed-vertex
transport theorem is blocked by the lifted positive top path being local to the
positive-step proof rather than a reusable definition.
