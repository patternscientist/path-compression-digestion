import PathCompressionDigestion.Basic

/-!
# Packet Ackermann normalization

This file defines the packet Ackermann function used in the paper:

* `A 0 x = 2 * x`;
* `A (i+1) 0 = 0`;
* `A (i+1) 1 = 2`;
* `A (i+1) (x+2) = A i (A (i+1) (x+1))`.

The main structural facts are currently scaffolded with `sorry`; each one
corresponds to the Ackermann package in paper Lemma 4.5 and its corollary.
-/

namespace PathCompressionDigestion

def A : Nat -> Nat -> Nat
  | 0, x => 2 * x
  | _ + 1, 0 => 0
  | i + 1, x + 1 => (A i)^[x] 2

@[simp] theorem A_zero (x : Nat) : A 0 x = 2 * x := rfl

@[simp] theorem A_succ_zero (i : Nat) : A (i + 1) 0 = 0 := rfl

@[simp] theorem A_succ_one (i : Nat) : A (i + 1) 1 = 2 := by
  simp [A]

@[simp] theorem A_succ_succ (i x : Nat) :
    A (i + 1) (x + 2) = A i (A (i + 1) (x + 1)) := by
  simp [A, Function.iterate_succ_apply']

namespace Ackermann

/-- Paper Lemma 4.5(1): each Ackermann row is monotone in the second argument. -/
theorem monotone_right (i : Nat) : Monotone (A i) := by
  sorry

/-- Paper Lemma 4.5(2): every positive row dominates the doubling row on `x >= 1`. -/
theorem ge_two_mul {i x : Nat} (hi : 1 <= i) (hx : 1 <= x) : 2 * x <= A i x := by
  sorry

/-- Paper Lemma 4.5(3): row domination for positive second argument. -/
theorem row_domination {i x : Nat} (hx : 1 <= x) : A i x <= A (i + 1) x := by
  sorry

/-- Paper Corollary after Lemma 4.5: the first positive row is exponentiation. -/
theorem one_eq_pow {y : Nat} (hy : 1 <= y) : A 1 y = 2 ^ y := by
  sorry

end Ackermann

end PathCompressionDigestion
