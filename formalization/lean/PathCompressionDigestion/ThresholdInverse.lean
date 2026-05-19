import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Defs

/-!
# Generic threshold inverses

This file supplies reusable infrastructure for the future concrete
formalization of the paper definition

`R_k(t) = max { r >= 0 : J_k r <= t }`.

It deliberately does not define the Seidel--Sharir `J` hierarchy, the
`diamond` operation, or any source recurrence.  Instead it packages the
minimal generic facts needed to build a threshold inverse for any natural-
valued function that is monotone, starts at zero, and eventually rises above
every finite threshold.
-/

namespace PathCompressionDigestion

namespace ThresholdInverse

/--
Data sufficient to define the finite maximum
`max { r : f r <= t }` for every natural threshold `t`.

The field `eventually_gt` gives a finite search bound for each threshold.
The field `zero_eq` gives the nonempty base witness, since `f 0 = 0 <= t`.
-/
structure Data where
  f : Nat -> Nat
  monotone : Monotone f
  zero_eq : f 0 = 0
  eventually_gt :
    forall t : Nat, exists B : Nat, forall r : Nat, B < r -> t < f r

namespace Data

variable (D : Data)

/-- A noncomputably chosen finite bound above all solutions of `f r <= t`. -/
noncomputable def upperBound (t : Nat) : Nat :=
  by
    classical
    exact Nat.find (D.eventually_gt t)

/-- The chosen bound really excludes all larger indices. -/
theorem upperBound_spec (t r : Nat) (h : D.upperBound t < r) : t < D.f r := by
  classical
  exact Nat.find_spec (D.eventually_gt t) r h

end Data

/-- Generic threshold inverse: the greatest `r` with `D.f r <= t`. -/
noncomputable def thresholdInverse (D : Data) (t : Nat) : Nat :=
  Nat.findGreatest (fun r => D.f r <= t) (D.upperBound t)

/-- The threshold inverse lies below the finite search bound used to define it. -/
theorem thresholdInverse_le_upperBound (D : Data) (t : Nat) :
    thresholdInverse D t <= D.upperBound t := by
  exact Nat.findGreatest_le (P := fun r => D.f r <= t) (D.upperBound t)

/-- Maximality: every index below threshold lies below the threshold inverse. -/
theorem le_thresholdInverse_of_apply_le (D : Data) {r t : Nat}
    (h : D.f r <= t) :
    r <= thresholdInverse D t := by
  have hbound : r <= D.upperBound t := by
    by_contra hnot
    have hgt : D.upperBound t < r := Nat.lt_of_not_ge hnot
    have hescape : t < D.f r := D.upperBound_spec t r hgt
    exact (Nat.not_lt_of_ge h) hescape
  exact Nat.le_findGreatest (P := fun r => D.f r <= t) hbound h

/-- The threshold inverse itself is below threshold. -/
theorem apply_thresholdInverse_le (D : Data) (t : Nat) :
    D.f (thresholdInverse D t) <= t := by
  apply Nat.findGreatest_spec (P := fun r => D.f r <= t) (m := 0)
  · exact Nat.zero_le (D.upperBound t)
  · rw [D.zero_eq]
    exact Nat.zero_le t

/--
Any index at most the threshold inverse is also below threshold.
This is the monotone-function half of the max characterization.
-/
theorem apply_le_of_le_thresholdInverse (D : Data) {r t : Nat}
    (h : r <= thresholdInverse D t) :
    D.f r <= t :=
  Nat.le_trans (D.monotone h) (apply_thresholdInverse_le D t)

/-- Threshold inverses are monotone in the threshold parameter. -/
theorem thresholdInverse_mono_threshold (D : Data) :
    Monotone (thresholdInverse D) := by
  intro t u htu
  apply le_thresholdInverse_of_apply_le (D := D)
  exact Nat.le_trans (apply_thresholdInverse_le D t) htu

/--
Function monotonicity, with the orientation used by the paper:
if `f2 r <= f1 r` pointwise, then the inverse for `f1` is bounded by the
inverse for `f2`.

For the future concrete hierarchy, `J_{k+1} <= J_k` will instantiate this as
`R_k(t) <= R_{k+1}(t)`.
-/
theorem thresholdInverse_mono_function {D1 D2 : Data}
    (h : forall r : Nat, D2.f r <= D1.f r) (t : Nat) :
    thresholdInverse D1 t <= thresholdInverse D2 t := by
  apply le_thresholdInverse_of_apply_le (D := D2)
  exact Nat.le_trans (h _) (apply_thresholdInverse_le D1 t)

end ThresholdInverse

end PathCompressionDigestion
