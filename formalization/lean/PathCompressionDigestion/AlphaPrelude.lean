import PathCompressionDigestion.MainComparison

/-!
# Generic alpha prelude

This file provides small, generic least-index and Ackermann-buffer facts for
later alpha/cost consequences.  It intentionally does not define the concrete
`J` hierarchy, the concrete inverse `R`, or any source recurrence machinery.
-/

namespace PathCompressionDigestion

namespace Ackermann

/-- Ackermann rows are monotone in the row index on positive inputs. -/
theorem monotone_left_of_pos {i j x : Nat} (hij : i <= j) (hx : 1 <= x) :
    A i x <= A j x := by
  induction j, hij using Nat.le_induction with
  | base =>
      rfl
  | succ j _ ih =>
      exact ih.trans (row_domination hx)

/-- Every Ackermann row takes the value `4` at input `2`. -/
theorem eval_two (i : Nat) : A i 2 = 4 := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [show 2 = 0 + 2 by norm_num, A_succ_succ, A_succ_one, ih]

/-- The Ackermann column `4 * Q` is monotone in `Q`. -/
theorem four_mul_column_mono {z Q Q' : Nat} (hQ : Q <= Q') :
    A z (4 * Q) <= A z (4 * Q') :=
  monotone_right z (Nat.mul_le_mul_left 4 hQ)

/-- A one-step `4 * Q` column buffer. -/
theorem four_mul_column_succ (z Q : Nat) :
    A z (4 * Q) <= A z (4 * (Q + 1)) :=
  four_mul_column_mono (z := z) (Nat.le_succ Q)

end Ackermann

/-- Positive thresholds are bounded by their `4 * Q` buffer. -/
theorem le_four_mul {Q : Nat} (hQ : 1 <= Q) : Q <= 4 * Q := by
  omega

namespace Abstract

noncomputable def alphaOf (R : ThresholdFamily) (target threshold : Nat) : Nat := by
  classical
  exact if h : Exists fun k : Nat => target <= R k threshold then Nat.find h else 0

/-- The chosen alpha index satisfies the threshold predicate when one exists. -/
theorem alpha_spec {R : ThresholdFamily} {target threshold : Nat}
    (h : Exists fun k : Nat => target <= R k threshold) :
    target <= R (alphaOf R target threshold) threshold := by
  classical
  simpa [alphaOf, h] using Nat.find_spec h

/-- The chosen alpha index is least among indices satisfying the threshold predicate. -/
theorem alpha_min {R : ThresholdFamily} {target threshold k : Nat}
    (hk : target <= R k threshold) :
    alphaOf R target threshold <= k := by
  classical
  let h : Exists fun j : Nat => target <= R j threshold := Exists.intro k hk
  simpa [alphaOf, h] using Nat.find_min' h hk

/-- Transitivity helper for feeding an Ackermann comparison into a threshold bound. -/
theorem target_le_R_of_le_ackermann_four_mul {R : ThresholdFamily} {target z Q : Nat}
    (hTarget : target <= A z (4 * Q))
    (hCompare : A z (4 * Q) <= R (z + 1) Q) :
    target <= R (z + 1) Q :=
  hTarget.trans hCompare

/-- Alpha-index comparison induced by an Ackermann-to-threshold comparison. -/
theorem alphaOf_le_succ_of_le_ackermann_four_mul {R : ThresholdFamily} {target z Q : Nat}
    (hTarget : target <= A z (4 * Q))
    (hCompare : A z (4 * Q) <= R (z + 1) Q) :
    alphaOf R target Q <= z + 1 :=
  alpha_min (target_le_R_of_le_ackermann_four_mul hTarget hCompare)

/-- Generic alpha consequence of the abstract main comparison. -/
theorem alphaOf_le_succ_of_main_comparison_from_core {R : ThresholdFamily}
    (H : ThresholdCoreAssumptions R) {target z Q : Nat}
    (hz : 1 <= z) (hQ : 1 <= Q) (hTarget : target <= A z (4 * Q)) :
    alphaOf R target Q <= z + 1 :=
  alphaOf_le_succ_of_le_ackermann_four_mul hTarget
    (main_comparison_from_core (R := R) H z Q hz hQ)

end Abstract

end PathCompressionDigestion
