import PathCompressionDigestion.JHierarchy
import PathCompressionDigestion.ThresholdInverseExtras

/-!
# Concrete threshold inverse for the `J` hierarchy

This file instantiates the generic threshold-inverse infrastructure for each
concrete row `J k`, then defines the paper's finite maximum

`R k t = max { r : J k r <= t }`.

It proves the easy concrete facts needed on the way to the abstract
`ThresholdCoreAssumptions` bridge.  The hard diamond-to-threshold recurrence is
left to the later concrete-core branch.
-/

namespace PathCompressionDigestion

/-- Threshold-inverse data for the concrete row `J k`. -/
def JThresholdData (k : Nat) : ThresholdInverse.Data :=
  ThresholdInverse.Data.of_monotone_unbounded
    (J k)
    (J_zero_arg k)
    (J_monotone k)
    (J_unbounded k)

/-- Concrete threshold inverse `R_k(t) = max { r : J k r <= t }`. -/
noncomputable def R (k t : Nat) : Nat :=
  ThresholdInverse.thresholdInverse (JThresholdData k) t

/-- The concrete threshold inverse itself is below the threshold. -/
theorem J_R_le (k t : Nat) :
    J k (R k t) <= t := by
  unfold R
  change (JThresholdData k).f
      (ThresholdInverse.thresholdInverse (JThresholdData k) t) <= t
  exact ThresholdInverse.apply_thresholdInverse_le (JThresholdData k) t

/-- Maximality of `R`: any row value below threshold has rank at most `R`. -/
theorem le_R_of_J_le {k r t : Nat}
    (h : J k r <= t) :
    r <= R k t := by
  unfold R
  exact ThresholdInverse.le_thresholdInverse_of_apply_le (D := JThresholdData k) (by
    change J k r <= t
    exact h)

/-- If a rank is above `R`, then it has already escaped the threshold. -/
theorem lt_J_of_R_lt {k r t : Nat}
    (h : R k t < r) :
    t < J k r := by
  by_contra hnot
  have hle : J k r <= t := Nat.le_of_not_gt hnot
  have hrle : r <= R k t := le_R_of_J_le hle
  exact (Nat.not_lt_of_ge hrle) h

/-- Threshold monotonicity of the concrete inverse. -/
theorem R_monotone_threshold (k : Nat) :
    Monotone (R k) := by
  intro t u htu
  unfold R
  exact ThresholdInverse.thresholdInverse_mono_threshold (JThresholdData k) htu

/-- Pointwise form of threshold monotonicity. -/
theorem R_mono_t {k t u : Nat}
    (h : t <= u) :
    R k t <= R k u :=
  R_monotone_threshold k h

/-- Level monotonicity of the concrete inverse. -/
theorem R_monotone_level (k t : Nat) :
    R k t <= R (k + 1) t := by
  unfold R
  exact
    ThresholdInverse.thresholdInverse_mono_function
      (D1 := JThresholdData k)
      (D2 := JThresholdData (k + 1))
      (fun r => by
        change J (k + 1) r <= J k r
        exact J_succ_le k r)
      t

/-- Exact base inverse for the concrete threshold family. -/
theorem R_zero_eq (t : Nat) :
    R 0 t = 2 * t + 1 := by
  have hgreatest := J0_base_inverse_isGreatest t
  apply le_antisymm
  next =>
    have hR : J0 (R 0 t) <= t := by
      simpa [J_zero_row] using J_R_le 0 t
    exact hgreatest.2 hR
  next =>
    have hbase : J 0 (2 * t + 1) <= t := by
      simpa [J_zero_row] using hgreatest.1
    exact le_R_of_J_le hbase

end PathCompressionDigestion
