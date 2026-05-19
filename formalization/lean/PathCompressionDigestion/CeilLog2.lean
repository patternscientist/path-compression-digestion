import Mathlib.Data.Nat.Log

/-!
# Natural ceiling log base two

This file isolates the Nat-valued ceiling logarithm facts needed for the
future formalization of the Seidel--Sharir diamond recursion.  We deliberately
use Mathlib's `Nat.clog`, the upper natural logarithm, rather than defining a
new search procedure: its Galois-style API already gives the power
characterization and monotonicity facts directly.

No `diamond`, concrete `J`, or threshold recurrence is defined here.
-/

namespace PathCompressionDigestion

/-- Natural-valued `ceil (log_2 x)`, with Mathlib's convention
`Nat.clog 2 0 = Nat.clog 2 1 = 0`. -/
def ceilLog2 (x : Nat) : Nat :=
  Nat.clog 2 x

@[simp] theorem ceilLog2_zero : ceilLog2 0 = 0 := by
  simp [ceilLog2]

@[simp] theorem ceilLog2_one : ceilLog2 1 = 0 := by
  simp [ceilLog2]

@[simp] theorem ceilLog2_two : ceilLog2 2 = 1 := by
  exact Nat.clog_eq_one (b := 2) (n := 2) le_rfl le_rfl

/-- Elementary exponential lower bound used to prove the termination estimate. -/
theorem self_le_two_pow_pred {x : Nat} (hx : 2 <= x) :
    x <= 2 ^ (x - 1) := by
  have h1 : 1 <= x := (by decide : 1 <= 2).trans hx
  have hsucc : x - 1 + 1 <= 2 ^ (x - 1) :=
    Nat.succ_le_of_lt ((show x - 1 < 2 ^ (x - 1) from Nat.lt_two_pow_self))
  simpa [Nat.sub_add_cancel h1] using hsucc

/-- Termination estimate matching the paper's `ceil(log_2 x) <= x - 1` for `x >= 2`. -/
theorem ceilLog2_le_pred {x : Nat} (hx : 2 <= x) :
    ceilLog2 x <= x - 1 := by
  exact Nat.clog_le_of_le_pow (b := 2) (self_le_two_pow_pred hx)

/-- Strict form of the termination estimate. -/
theorem ceilLog2_lt_self {x : Nat} (hx : 2 <= x) :
    ceilLog2 x < x := by
  exact (ceilLog2_le_pred hx).trans_lt
    (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hx) (by decide : 0 < 1))

/-- The ceiling logarithm is monotone. -/
theorem monotone_ceilLog2 : Monotone ceilLog2 := by
  intro x y hxy
  exact Nat.clog_mono_right 2 hxy

/-- Power upper characterization: every input is bounded by the corresponding power of two. -/
theorem le_two_pow_ceilLog2 (x : Nat) :
    x <= 2 ^ ceilLog2 x := by
  exact Nat.le_pow_clog Nat.one_lt_two x

/-- Minimality of `ceilLog2`: any power-of-two upper bound bounds `ceilLog2`. -/
theorem ceilLog2_le_of_le_two_pow {x k : Nat} (h : x <= 2 ^ k) :
    ceilLog2 x <= k := by
  exact Nat.clog_le_of_le_pow (b := 2) h

end PathCompressionDigestion
