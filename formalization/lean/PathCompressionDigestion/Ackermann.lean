import PathCompressionDigestion.Basic

/-!
# Packet Ackermann normalization

This file defines the packet Ackermann function used in the paper:

* `A 0 x = 2 * x`;
* `A (i+1) 0 = 0`;
* `A (i+1) 1 = 2`;
* `A (i+1) (x+2) = A i (A (i+1) (x+1))`.

The main structural facts correspond to the Ackermann package in paper
Lemma 4.5 and its corollary.
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

/-- Every positive Ackermann row dominates the doubling function, including at `0`. -/
theorem ge_two_mul_succ (i x : Nat) : 2 * x <= A (i + 1) x := by
  induction i generalizing x with
  | zero =>
      induction x with
      | zero =>
          simp
      | succ x ihx =>
          cases x with
          | zero =>
              simp
          | succ x =>
              rw [A_succ_succ, A_zero]
              nlinarith
  | succ i ih =>
      induction x with
      | zero =>
          simp
      | succ x ihx =>
          cases x with
          | zero =>
              simp
          | succ x =>
              rw [A_succ_succ]
              have harg : 2 * A (i + 2) (x + 1) <= A (i + 1) (A (i + 2) (x + 1)) :=
                ih (A (i + 2) (x + 1))
              nlinarith

/-- Each Ackermann row dominates the identity. -/
theorem self_le (i x : Nat) : x <= A i x := by
  cases i with
  | zero =>
      simp [A]
      omega
  | succ i =>
      have h := ge_two_mul_succ i x
      nlinarith

/-- Adjacent-step monotonicity in the second argument. -/
theorem le_succ_right (i x : Nat) : A i x <= A i (x + 1) := by
  cases i with
  | zero =>
      simp [A]
  | succ i =>
      cases x with
      | zero =>
          simp
      | succ x =>
          rw [A_succ_succ]
          exact self_le i (A (i + 1) (x + 1))

/-- Paper Lemma 4.5(1): each Ackermann row is monotone in the second argument. -/
theorem monotone_right (i : Nat) : Monotone (A i) := by
  exact monotone_nat_of_le_succ (le_succ_right i)

/-- Paper Lemma 4.5(2): every positive row dominates the doubling row on `x >= 1`. -/
theorem ge_two_mul {i x : Nat} (hi : 1 <= i) (hx : 1 <= x) : 2 * x <= A i x := by
  cases i with
  | zero =>
      omega
  | succ i =>
      have h := ge_two_mul_succ i x
      have hx' : 1 <= x := hx
      omega

/-- Paper Lemma 4.5(3): row domination for positive second argument. -/
theorem row_domination {i x : Nat} (hx : 1 <= x) : A i x <= A (i + 1) x := by
  cases x with
  | zero =>
      omega
  | succ x =>
      cases x with
      | zero =>
          cases i <;> simp
      | succ x =>
          rw [A_succ_succ]
          apply monotone_right i
          have hgrowth := ge_two_mul_succ i (x + 1)
          omega

/-- The first positive Ackermann row is exponentiation, shifted to positive inputs. -/
theorem one_eq_pow_succ (y : Nat) : A 1 (y + 1) = 2 ^ (y + 1) := by
  induction y with
  | zero =>
      simp
  | succ y ih =>
      rw [A_succ_succ, A_zero, ih]
      simp [pow_succ, Nat.mul_comm]

/-- Paper Corollary after Lemma 4.5: the first positive row is exponentiation. -/
theorem one_eq_pow {y : Nat} (hy : 1 <= y) : A 1 y = 2 ^ y := by
  cases y with
  | zero =>
      omega
  | succ y =>
      exact one_eq_pow_succ y

end Ackermann

end PathCompressionDigestion
