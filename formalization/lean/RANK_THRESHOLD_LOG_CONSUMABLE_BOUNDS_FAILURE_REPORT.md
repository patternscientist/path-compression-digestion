# Rank-Threshold Log Consumable Bounds Failure Report

Branch: `lean-rank-threshold-log-consumable-bounds-v1`

Starting base:

```text
origin/main = 0fef434a52f821a164366b34f7fb1610699d10a9
requested merged prerequisite = 64f0cc8dd353aa61443aae5303d7fa57e62eca50
```

## Summary

This worker did not prove:

```lean
RawCompressionExecution.RankThresholdLogConsumableBounds
```

Instead, it proved that the package was not unconditional for the pre-repair
finite skeleton:

```lean
theorem RawCompressionExecution.exists_legacyValidExecution_without_rankThresholdTopPacking_current_model :
    Exists fun E : RawCompressionExecution 1 1 4 =>
      Exists fun hE : E.IsLegacyValidWithoutRankPacking =>
        let i0 : Fin 1 := { val := 0, isLt := by omega }
        RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 1 ->
          False
```

Therefore this branch did not derive an unconditional:

```lean
theorem topDown_shift_step :
    forall k : Nat, topDownShiftStepTarget k
```

The already-merged source-shift arithmetic remains intact and should not be
redone.  The first missing field of `RankThresholdLogConsumableBounds` is the
rank-threshold top-packing witness.  The current concrete source model exposes
only parent-rank monotonicity through `RawRankedForest.IsRankValid`; it does
not carry the subtree/size accounting invariant needed to construct the
`TopPacking` injection.

## Exact Package Fields

The package is:

```lean
def RawCompressionExecution.RankThresholdLogConsumableBounds
    (Drow : DiamondInput)
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < Drow.g r),
    let s := ceilLog2 (Drow.g r)
    let i0 : Fin m := { val := 0, isLt := by omega }
    Exists fun P : RankThresholdDissection.TopPacking (E.step i0).before
        (hE.1 i0).1.1 s =>
      bottomConsumableBound /\ topConsumableBound
```

where the three concrete fields are:

1. Top packing:

```lean
RankThresholdDissection.TopPacking (E.step i0).before
  (hE.1 i0).1.1 s
```

2. Bottom consumable-cost simulation:

```lean
(E.canonicalBottomProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
  (k + 1) *
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
    2 *
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
      Drow.diamond s
```

3. Top consumable-cost simulation:

```lean
(E.canonicalTopProjectedExecution hE.1
  (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
  k *
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
    2 *
      ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
      Drow.g (r - s - 1)
```

The charged-count bookkeeping itself is already consumed downstream by:

```lean
RawCompressionExecution.rankThreshold_projected_nonroot_count_le
RawCompressionPath.ProjectedCompressionExecution.chargedCount_le_length
RawCompressionExecution.rankThreshold_source_cost_le_diamond_budget_of_consumable_bounds
RawCompressionExecution.rankThreshold_source_cost_le_diamond_budget_of_log_consumable_bounds
```

## Fields Already Derivable From Existing Lemmas

The downstream uses of the fields are already derivable once the fields are
supplied:

- `rankThresholdDissectionFamily_two_mul_top_card_mul_g_le` consumes
  `TopPacking` and the logarithmic bound `Drow.g r <= 2 ^ s`.
- `rankThreshold_source_cost_le_diamond_budget_of_consumable_bounds` consumes
  top packing, bottom simulation, top simulation, and charged-count
  bookkeeping.
- `rankThreshold_source_cost_le_diamond_budget_of_log_consumable_bounds`
  specializes the previous theorem to `s = ceilLog2 (Drow.g r)`.
- `sourceShiftStep_of_rankThreshold_log_consumable_bounds` turns the package
  into `SourceShiftStep topDownCost k Drow`.
- `topDown_shift_step_of_rankThreshold_log_consumable_bounds` specializes this
  to `(JInput k)`.

No field of the package itself is currently derivable unconditionally from
`RawCompressionExecution.IsValid`.

## First Failed Field

The first field that fails is top packing:

```lean
RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 s
```

This is not Nat arithmetic.  `TopPacking` is a concrete injection:

```lean
(dissection F hF s).topFinset -> Fin (2 ^ (s + 1)) -> Fin n
```

and therefore implies:

```lean
(dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n
```

This branch adds the diagnostic lemma:

```lean
theorem RankThresholdDissection.not_topPacking_of_top_card_mul_pow_gt
    (hF : F.IsRankValid)
    (s : Nat)
    (hgt : n < (dissection F hF s).topFinset.card * 2 ^ (s + 1)) :
    TopPacking F hF s -> False
```

The current model has no invariant preventing high-rank roots in tiny forests.
Thus `IsRankValid` alone cannot produce `TopPacking`; the missing ingredient is
source-faithful rank-size/subtree accounting, not a rearrangement of the shift
arithmetic.

After the model-repair branch, the theorem
`exists_legacyValidExecution_without_rankThresholdTopPacking_current_model`
keeps the standalone obstruction for the old skeleton without rank-threshold
packing.  The repaired faithful model proves:

```lean
def RawCompressionExecution.rankThresholdDissectionFamily_topPacking

theorem RawCompressionExecution.not_exists_validExecution_without_rankThresholdTopPacking_current_model
```

Thus the old one-vertex high-rank root is no longer accepted by the repaired
`RawCompressionExecution.IsValid`; it remains accepted only by the explicitly
named legacy predicate.

## Blocker Classification

Blocker: top packing first.

Secondary blockers, after top packing is supplied:

- bottom consumable-cost simulation;
- top consumable-cost simulation.

The charged-count bookkeeping needed by the existing log/diamond budget theorem
is already present.  The failure is not in the packaged source-shift arithmetic
and not in the existing finite paper theorem bridge.

## Smallest Next Theorem Statement

The smallest theorem over the current package shape is:

```lean
theorem rankThresholdLogTopPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    RankThresholdDissection.TopPacking (E.step i0).before
      (hE.1 i0).1.1 s
```

However, the new counterexample theorem shows that this statement is not sound
for the present concrete model unless `RawCompressionExecution.IsValid` is
strengthened, or accompanied, by a source-faithful rank-size/subtree packing
invariant.  A sound next step should first add and audit that invariant, then
prove the top-packing theorem from it while preserving the existing
`RankThresholdLogConsumableBounds` wrapper.

## Verdict

Ambition D achieved for the original worker.  The exact package fields are
identified, the downstream fields already consumed by existing lemmas are
separated from the missing fields, and the first blocker was mechanically
isolated as top packing.  The later model-repair branch fixes that top-packing
defect by adding direct rank-threshold packing to the faithful base/rank
accounting layer.

No unconditional `RankThresholdLogConsumableBounds`, `topDown_shift_step`,
`SourceRecurrence topDownCost`, or paper-facing finite theorem is claimed.
