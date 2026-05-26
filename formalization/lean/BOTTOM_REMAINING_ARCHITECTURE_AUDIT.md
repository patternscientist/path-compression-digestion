# Bottom Remaining Architecture Audit

Branch: `lean-bottom-positive-core-v1`

Starting base required by the task:

```text
d9b0dfe88c805420105a511c55ac8ad8a54b820f
```

Inspected commit:

```text
c81548c9df723c57c787f91cb002d589d61e7aab
```

## 1. Expanded Positive-Core Target

The exact current positive-core target is:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (_hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    0 < Cb.chargedCount ->
      1 <= Bcard ->
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
          topDownCost Cb.chargedCount Bcard s
```

This is the nondegenerate subcase of:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomChargedProjectedTopDownCostBounds
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (_hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      topDownCost Cb.chargedCount Bcard s
```

The bridge
`rankThresholdJInputBottomChargedProjectedTopDownCostBounds_of_positiveCore`
uses the zero charged-count case and the positive-count-to-nonempty-bottom-card
lemma to recover the full charged-projected `topDownCost` bound from the
positive core.

## 2. `topDownCost` Definition And API

The exact definition is:

```lean
noncomputable def topDownCost : SourceCostFamily :=
  fun m n r => by
    classical
    exact
    ((Finset.univ : Finset (RawCompressionExecution m n r)).filter
        fun E => E.IsValid).sup fun E => E.cost
```

The lower-bound API is only extremal over genuine valid ordinary executions:

```lean
theorem RawCompressionExecution.cost_le_topDownCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid) :
    E.cost <= topDownCost m n r
```

The upper-bound API is:

```lean
theorem topDownCost_le_of_forall_valid
    {m n r B : Nat}
    (h : forall E : RawCompressionExecution m n r, E.IsValid -> E.cost <= B) :
    topDownCost m n r <= B

theorem topDownCost_le_base_budget (m n r : Nat) :
    topDownCost m n r <= n * (r - 1)
```

The relevant zero lemmas are:

```lean
theorem topDownCost_rank_zero_eq_zero (m n : Nat) :
    topDownCost m n 0 = 0

theorem RawCompressionExecution.topDownCost_zero_length_eq_zero (n r : Nat) :
    topDownCost 0 n r = 0

theorem RawCompressionExecution.topDownCost_one_vertex_eq_zero (m r : Nat) :
    topDownCost m 1 r = 0
```

No general monotonicity or padding theorem for `topDownCost` is present in the
current API. The only way to prove a lower bound on `topDownCost` is to exhibit
a valid `RawCompressionExecution` with that cost.

## 3. Verdict On The `s * chargedCount` Absorption Route

The diagnostic theorem added on this branch is:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomChargedProjectedExecution_cost_le_threshold_mul_chargedCount
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      s *
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount
```

This does not close the positive core. The required extra theorem would be:

```lean
s * Cb.chargedCount <= topDownCost Cb.chargedCount Bcard s
```

or an equivalent lower bound with the exact arguments
`topDownCost Cb.chargedCount Bcard s`. This route is not viable:

1. `topDownCost` has no lower-bound API except `E.cost_le_topDownCost` for a
   valid ordinary execution.
2. The coefficient bound is only a per-slot range estimate; it has no
   recurrence structure and no ordinary consecutive-state witness.
3. The proposed lower bound is arithmetically incompatible with the base upper
   bound in general. Since
   `topDownCost Cb.chargedCount Bcard s <= Bcard * (s - 1)`, a universal
   theorem `s * Cb.chargedCount <= topDownCost Cb.chargedCount Bcard s` would
   force `s * Cb.chargedCount <= Bcard * (s - 1)`, which is not a consequence
   of the positive-core hypotheses.
4. The zero and one-vertex API also shows the danger of treating projected cost
   as ordinary recurrence cost: `topDownCost m 1 r = 0`, while generic
   projected admissible executions can have positive projected cost.

So the `s * chargedCount` theorem is useful only as a diagnostic local range
bound. It should not be the consumer theorem.

## 4. Verdict On Synthetic Ordinary Execution

The synthetic ordinary execution route should not be pursued in the old
charged-only form. The diagnostic premise

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomChargedSkeletonConsecutive (k : Nat) : Prop := ...
```

would imply the sharp charged-projected `topDownCost` premise, but it is the
wrong object: the charged-only skeleton skips source-relevant uncharged bottom
boundary exceptions, and those skipped slots can change the bottom projected
parent map.

The checked obstruction includes:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomBoundaryExceptionSlot_changes_projected_parent

theorem RawCompressionExecution
  .rankThresholdBottomBoundaryExceptionSlot_rootLike_pos_not_noop
```

Ordinary no-op/rootpath padding is therefore not a faithful repair for those
boundary exceptions.

## 5. Verdict On Boundary-Taxed Projected Consumer

This is the recommended remaining theorem shape.

The current code already contains the right consumer interface:

```lean
def RawCompressionExecution
  .RankThresholdJInputBottomTaxedTopDownCostBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost + X <= topDownCost Cb.chargedCount Bcard s + Bcard
```

This is exactly the boundary-taxed projected consumer: the charged projected
part is paid by one recurrence call, while the source-relevant bottom boundary
exception contribution is paid by the stable bottom-card tax.

The boundary-card accounting already exists:

```lean
theorem RawCompressionExecution
  .rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s) <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
```

The projected boundary-inclusive execution also exposes the same cost:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_cost_eq_consumable_add_boundary
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    (E.rankThresholdBottomRelevantProjectedExecution hE s).cost =
      Cb.consumableCost + X
```

So an equivalent projected-object theorem can be stated as:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_cost_le_topDownCost_add_bottomCard
    (k : Nat)
    {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    (E.rankThresholdBottomRelevantProjectedExecution hE s).cost <=
      topDownCost Cb.chargedCount Bcard s + Bcard
```

This theorem is equivalent to the existing taxed-field statement after rewriting
with `rankThresholdBottomRelevantProjectedExecution_cost_eq_consumable_add_boundary`.

## 6. Existing Internal Fields

`RankThresholdJInputBottomConsumableBounds` is not wrong, but it is too eager as
the next bottom theorem. It asks for the already-absorbed algebraic bottom
bound:

```lean
Cb.consumableCost <=
  (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s
```

That shape hides the needed smaller-rank recurrence call. The current
tax-aware bridge correctly avoids deriving this field directly.

`RankThresholdJInputBottomChargedProjectedTopDownCostPositiveCore` is
wrong-shaped as the next proof-worker target. It asks for a charged-only
projected `topDownCost` lower bound, excluding the source-relevant boundary
state changes that explain why the old skeleton route failed. It can remain as
a diagnostic or optional stronger theorem, but it should not be the selected
remaining theorem.

`RankThresholdJInputBottomTaxedTopDownCostBounds` is the right replacement
internal field. It already closes the source shift through:

```lean
theorem RawCompressionExecution
  .topDown_shift_step_of_rankThresholdJInputBottomTaxedTopDownCostBounds
    (k : Nat)
    (hbottomTax : RankThresholdJInputBottomTaxedTopDownCostBounds k) :
    topDownShiftStepTarget k
```

This preserves the paper-facing theorem names and constants, and does not add
`topDown_shift_step` or `RankThresholdJInputConsumableBounds` as certificate
fields.

## 7. Recommended Next Theorem Statement

Use the existing field as the canonical target:

```lean
theorem RawCompressionExecution
  .rankThresholdJInputBottomTaxedTopDownCostBounds_closed
    (k : Nat) :
    RankThresholdJInputBottomTaxedTopDownCostBounds k
```

For a more local projected-object worker target, use:

```lean
theorem RawCompressionExecution
  .rankThresholdBottomRelevantProjectedExecution_cost_le_topDownCost_add_bottomCard
    (k : Nat)
    {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r) :
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := Fin.mk 0 (by omega)
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    (E.rankThresholdBottomRelevantProjectedExecution hE s).cost <=
      topDownCost Cb.chargedCount Bcard s + Bcard
```

Then prove `RankThresholdJInputBottomTaxedTopDownCostBounds k` by rewriting the
left side with
`rankThresholdBottomRelevantProjectedExecution_cost_eq_consumable_add_boundary`.

## 8. Next Proof-Worker Prompt

```text
Use the current branch. Do not target
RawCompressionExecution.RankThresholdJInputBottomChargedSkeletonConsecutive.
Do not prove the charged-only positive core as the main route.

Target the boundary-taxed projected consumer:

  theorem RawCompressionExecution
    .rankThresholdJInputBottomTaxedTopDownCostBounds_closed
      (k : Nat) :
      RankThresholdJInputBottomTaxedTopDownCostBounds k

or first prove the local projected-object theorem:

  theorem RawCompressionExecution
    .rankThresholdBottomRelevantProjectedExecution_cost_le_topDownCost_add_bottomCard
      (k : Nat)
      {m n r : Nat}
      (hm : 1 <= m)
      (_hn : 1 <= n)
      (hprev : SourceBound topDownCost k (JInput k).g)
      (E : RawCompressionExecution m n r)
      (hE : E.IsValid)
      (_hlarge : 1 < (JInput k).g r) :
      let s := ceilLog2 ((JInput k).g r)
      let i0 : Fin m := Fin.mk 0 (by omega)
      let Cb :=
        E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)
      let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
      (E.rankThresholdBottomRelevantProjectedExecution hE s).cost <=
        topDownCost Cb.chargedCount Bcard s + Bcard

Use the existing boundary-card theorem
rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card and
the existing cost identity
rankThresholdBottomRelevantProjectedExecution_cost_eq_consumable_add_boundary.
Do not package source-relevant boundary exceptions as ordinary no-op/rootpath
steps. Preserve the paper-facing theorem statements and constants.
```

## Final Verdict

ARCHITECTURE_SELECTED.

The selected remaining theorem shape is the boundary-taxed projected consumer,
with `RankThresholdJInputBottomTaxedTopDownCostBounds` as the internal field to
close the shift. The `s * chargedCount` theorem is diagnostic only, and the
charged-only synthetic ordinary execution route should remain a documented
non-route.
