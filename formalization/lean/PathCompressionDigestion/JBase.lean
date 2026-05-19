import PathCompressionDigestion.Basic

/-!
# Concrete base row

This file formalizes only the base row of the paper's `J` hierarchy.  It does
not define `diamond`, recursive rows, alpha, or cost consequences.

For natural ranks, `r / 2` agrees with the source formula
`ceil((r - 1) / 2)`:

```text
r = 0 -> 0, r = 1 -> 0, r = 2 -> 1, r = 3 -> 1, ...
```
-/

namespace PathCompressionDigestion

/-- Concrete base row corresponding to the source formula `J_0(r) = ceil((r - 1) / 2)`. -/
def J0 (r : Nat) : Nat :=
  r / 2

@[simp] theorem J0_zero : J0 0 = 0 := by
  norm_num [J0]

@[simp] theorem J0_one : J0 1 = 0 := by
  norm_num [J0]

@[simp] theorem J0_two : J0 2 = 1 := by
  norm_num [J0]

/-- The concrete base row is monotone in the rank. -/
theorem J0_monotone : Monotone J0 := by
  intro r s hrs
  exact Nat.div_le_div_right hrs

/-- Source-style strictness for the base row: above rank `1`, `J_0(r) < r`. -/
theorem J0_lt_self {r : Nat} (hr : r > 1) : J0 r < r := by
  exact Nat.div_lt_self (Nat.zero_lt_of_lt hr) (by norm_num : 1 < 2)

/--
Exact threshold characterization for the base row.

This is the Lean form of the paper's calculation
`J_0(r) <= t` iff `r <= 2*t + 1`.
-/
theorem J0_le_iff_le_two_mul_add_one (r t : Nat) :
    J0 r <= t <-> r <= 2 * t + 1 := by
  unfold J0
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)]

/-- The paper's exact base inverse lower witness, `R_0(t) = 2*t + 1`. -/
theorem J0_base_inverse_lower (t : Nat) : J0 (2 * t + 1) <= t :=
  (J0_le_iff_le_two_mul_add_one (2 * t + 1) t).2 le_rfl

/-- The paper's exact base inverse upper bound, `R_0(t) = 2*t + 1`. -/
theorem J0_base_inverse_upper {r t : Nat} (h : J0 r <= t) : r <= 2 * t + 1 :=
  (J0_le_iff_le_two_mul_add_one r t).1 h

/--
Standalone max-characterization of the exact base inverse:
`2*t + 1` is the largest rank satisfying `J_0(r) <= t`.
-/
theorem J0_base_inverse (t : Nat) :
    J0 (2 * t + 1) <= t
      /\ forall r : Nat, J0 r <= t -> r <= 2 * t + 1 := by
  constructor
  next =>
    exact J0_base_inverse_lower t
  next =>
    intro r h
    exact J0_base_inverse_upper h

/-- Set-theoretic largest-element form of the exact base inverse `R_0(t) = 2*t + 1`. -/
theorem J0_base_inverse_isGreatest (t : Nat) :
    IsGreatest {r : Nat | J0 r <= t} (2 * t + 1) := by
  constructor
  next =>
    exact J0_base_inverse_lower t
  next =>
    intro r hr
    exact J0_base_inverse_upper hr

end PathCompressionDigestion
