import PathCompressionDigestion.Diamond
import PathCompressionDigestion.ThresholdInverseExtras

/-!
# Generic diamond-to-threshold recurrence

This file packages threshold inverses for a `DiamondInput` row and for its
diamond transform, then proves the generic recurrence used by the concrete
`J` hierarchy:

```text
Rg (2 ^ Rdiamond t) <= Rdiamond (t + 1).
```

It deliberately does not define the concrete threshold family `R k t`.
-/

namespace PathCompressionDigestion

namespace DiamondInput

/-- Threshold-inverse data for the original row of a `DiamondInput`. -/
def gThresholdData (D : DiamondInput) : ThresholdInverse.Data :=
  ThresholdInverse.Data.of_monotone_unbounded D.g D.zero_eq D.monotone D.unbounded

/-- Threshold-inverse data for the diamond transform of a `DiamondInput`. -/
def diamondThresholdData (D : DiamondInput) : ThresholdInverse.Data :=
  ThresholdInverse.Data.of_monotone_unbounded D.diamond D.diamond_zero
    D.diamond_monotone D.diamond_unbounded

/-- Threshold inverse for the original row of a `DiamondInput`. -/
noncomputable def Rg (D : DiamondInput) (t : Nat) : Nat :=
  ThresholdInverse.thresholdInverse D.gThresholdData t

/-- Threshold inverse for the diamond transform of a `DiamondInput`. -/
noncomputable def Rdiamond (D : DiamondInput) (t : Nat) : Nat :=
  ThresholdInverse.thresholdInverse D.diamondThresholdData t

/--
Generic diamond-to-threshold recurrence.

For any packaged row `g` and its diamond transform `h`, the threshold inverse
of `h` at `t + 1` dominates the threshold inverse of `g` at `2 ^ Rh(t)`.
-/
theorem threshold_step (D : DiamondInput) (t : Nat) :
    D.Rg (2 ^ (D.Rdiamond t)) <= D.Rdiamond (t + 1) := by
  change D.Rg (2 ^ (D.Rdiamond t)) <=
    ThresholdInverse.thresholdInverse D.diamondThresholdData (t + 1)
  apply ThresholdInverse.le_thresholdInverse_of_apply_le (D := D.diamondThresholdData)
  change D.diamond (D.Rg (2 ^ (D.Rdiamond t))) <= t + 1
  let r : Nat := D.Rg (2 ^ (D.Rdiamond t))
  change D.diamond r <= t + 1
  have hg_r : D.g r <= 2 ^ (D.Rdiamond t) := by
    dsimp [r, Rg]
    simpa [gThresholdData] using
      ThresholdInverse.apply_thresholdInverse_le D.gThresholdData (2 ^ (D.Rdiamond t))
  by_cases hsmall : D.g r <= 1
  case pos =>
    rw [D.diamond_eq_small hsmall]
    exact hsmall.trans (by simp)
  case neg =>
    have hlarge : 1 < D.g r := Nat.lt_of_not_ge hsmall
    have hlog_le : ceilLog2 (D.g r) <= D.Rdiamond t :=
      ceilLog2_le_of_le_two_pow hg_r
    have hdiamond_log : D.diamond (ceilLog2 (D.g r)) <= t := by
      have hraw :
          D.diamondThresholdData.f (ceilLog2 (D.g r)) <= t :=
        ThresholdInverse.apply_le_of_le_thresholdInverse
          (D := D.diamondThresholdData)
          (r := ceilLog2 (D.g r))
          (t := t)
          (by
            simpa [Rdiamond] using hlog_le)
      simpa [diamondThresholdData] using hraw
    rw [D.diamond_eq_large hlarge]
    simpa [Nat.add_comm] using Nat.add_le_add_left hdiamond_log 1

end DiamondInput

end PathCompressionDigestion
