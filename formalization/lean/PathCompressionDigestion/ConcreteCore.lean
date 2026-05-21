import PathCompressionDigestion.ConcreteThreshold
import PathCompressionDigestion.DiamondThreshold
import PathCompressionDigestion.MainComparison

/-!
# Concrete threshold core

This file bridges the concrete threshold inverse family `R` for the recursive
`J` hierarchy to the abstract threshold-core interface used by the comparison
theorem.
-/

namespace PathCompressionDigestion

/-- The concrete `R k` is the generic threshold inverse for `JInput k`. -/
theorem R_eq_Rg_JInput (k t : Nat) :
    R k t = (JInput k).Rg t := by
  rfl

/-- The concrete successor row inverse is the diamond inverse for `JInput k`. -/
theorem R_succ_eq_Rdiamond_JInput (k t : Nat) :
    R (k + 1) t = (JInput k).Rdiamond t := by
  rfl

/-- The concrete threshold inverse family satisfies the abstract core package. -/
theorem concrete_threshold_core_assumptions :
    Abstract.ThresholdCoreAssumptions R := by
  refine
    { baseExact := R_zero_eq
      monotoneThreshold := R_monotone_threshold
      monotoneLevel := R_monotone_level
      thresholdStep := ?_ }
  intro k t
  rw [R_eq_Rg_JInput k, R_succ_eq_Rdiamond_JInput k]
  exact DiamondInput.threshold_step (JInput k) t

/-- Concrete main comparison, obtained directly from the abstract theorem. -/
theorem concrete_main_comparison :
    forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q :=
  Abstract.main_comparison_from_core concrete_threshold_core_assumptions

end PathCompressionDigestion
