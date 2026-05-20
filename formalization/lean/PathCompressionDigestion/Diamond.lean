import PathCompressionDigestion.Basic
import PathCompressionDigestion.CeilLog2

/-!
# Concrete diamond transform

This file formalizes the paper's `g^diamond` transform for natural-valued
functions satisfying the hypotheses used by the Seidel--Sharir hierarchy:
monotonicity, unboundedness, a zero value at zero, and strict descent below
the identity on positive inputs.

It does not define the recursive concrete `J_k` hierarchy.  The definitions
and lemmas here are intended to be reused by that later file.
-/

namespace PathCompressionDigestion

/-- Hypotheses needed to define and preserve the paper's `g^diamond` transform. -/
structure DiamondInput where
  g : Nat -> Nat
  zero_eq : g 0 = 0
  monotone : Monotone g
  unbounded : forall t : Nat, exists r : Nat, t <= g r
  lt_self_pos : forall {r : Nat}, 0 < r -> g r < r

namespace DiamondInput

variable (D : DiamondInput)

/-- If `g r > 1`, then the logarithmic recursive argument is smaller than `r`. -/
theorem ceilLog2_g_lt_of_large {r : Nat} (hlarge : 1 < D.g r) :
    ceilLog2 (D.g r) < r := by
  have hg_two : 2 <= D.g r := by omega
  have hg_pos : 0 < D.g r := by omega
  have hr_pos : 0 < r := by
    by_contra hnot
    have hr : r = 0 := Nat.eq_zero_of_not_pos hnot
    have hg0 : D.g r = 0 := by simpa [hr] using D.zero_eq
    omega
  have hlog : ceilLog2 (D.g r) <= D.g r - 1 :=
    ceilLog2_le_pred hg_two
  have hg_pred_lt : D.g r - 1 < r := by
    have hg_lt : D.g r < r := D.lt_self_pos hr_pos
    omega
  exact lt_of_le_of_lt hlog hg_pred_lt

/-- The paper's diamond transform `g^diamond`. -/
def diamond : Nat -> Nat
  | r =>
      if hsmall : D.g r <= 1 then
        D.g r
      else
        1 + diamond (ceilLog2 (D.g r))
termination_by r => r
decreasing_by
  exact D.ceilLog2_g_lt_of_large (Nat.lt_of_not_ge hsmall)

theorem diamond_eq_small {r : Nat} (hsmall : D.g r <= 1) :
    D.diamond r = D.g r := by
  rw [diamond]
  simp [hsmall]

theorem diamond_eq_large {r : Nat} (hlarge : 1 < D.g r) :
    D.diamond r = 1 + D.diamond (ceilLog2 (D.g r)) := by
  rw [diamond]
  simp [Nat.not_le_of_gt hlarge]

theorem diamond_zero : D.diamond 0 = 0 := by
  have hsmall : D.g 0 <= 1 := by
    rw [D.zero_eq]
    omega
  rw [diamond_eq_small D hsmall, D.zero_eq]

/-- For every argument, `g r <= r`. -/
theorem g_le_self (r : Nat) : D.g r <= r := by
  cases r with
  | zero =>
      rw [D.zero_eq]
  | succ r =>
      exact Nat.le_of_lt (D.lt_self_pos (Nat.succ_pos r))

/-- The diamond transform is pointwise bounded by its input function. -/
theorem diamond_le_g (r : Nat) : D.diamond r <= D.g r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hsmall : D.g r <= 1
      case pos =>
        rw [diamond_eq_small D hsmall]
      case neg =>
        have hlarge : 1 < D.g r := Nat.lt_of_not_ge hsmall
        set u : Nat := ceilLog2 (D.g r)
        have hu_lt : u < r := by
          simpa [u] using D.ceilLog2_g_lt_of_large hlarge
        have hrec : D.diamond u <= D.g u := ih u hu_lt
        have hgu_le_u : D.g u <= u := D.g_le_self u
        have hu_le_pred : u <= D.g r - 1 := by
          simpa [u] using ceilLog2_le_pred (by omega : 2 <= D.g r)
        rw [diamond_eq_large D hlarge]
        have hdu_le_u : D.diamond u <= u := hrec.trans hgu_le_u
        have hmain : 1 + D.diamond u <= D.g r := by
          omega
        simpa [u] using hmain

/-- The diamond transform also strictly descends below the identity on positive inputs. -/
theorem diamond_lt_self_pos {r : Nat} (hr : 0 < r) : D.diamond r < r := by
  exact lt_of_le_of_lt (D.diamond_le_g r) (D.lt_self_pos hr)

/-- The diamond transform is monotone. -/
theorem diamond_monotone : Monotone D.diamond := by
  intro r s hrs
  induction s using Nat.strong_induction_on generalizing r with
  | h s ih =>
      have hg_rs : D.g r <= D.g s := D.monotone hrs
      by_cases hs_small : D.g s <= 1
      case pos =>
        have hr_small : D.g r <= 1 := le_trans hg_rs hs_small
        rw [diamond_eq_small D hr_small, diamond_eq_small D hs_small]
        exact hg_rs
      case neg =>
        have hs_large : 1 < D.g s := Nat.lt_of_not_ge hs_small
        by_cases hr_small : D.g r <= 1
        case pos =>
          rw [diamond_eq_small D hr_small, diamond_eq_large D hs_large]
          omega
        case neg =>
          have hr_large : 1 < D.g r := Nat.lt_of_not_ge hr_small
          set u : Nat := ceilLog2 (D.g r)
          set v : Nat := ceilLog2 (D.g s)
          have hu_le_v : u <= v := by
            exact monotone_ceilLog2 hg_rs
          have hv_lt_s : v < s := by
            simpa [v] using D.ceilLog2_g_lt_of_large hs_large
          have hrec : D.diamond u <= D.diamond v := ih v hv_lt_s (r := u) hu_le_v
          rw [diamond_eq_large D hr_large, diamond_eq_large D hs_large]
          have hmain : 1 + D.diamond u <= 1 + D.diamond v := by
            omega
          simpa [u, v] using hmain

/-- A strict lower-bound direction for the ceiling logarithm. -/
theorem lt_ceilLog2_of_pow_lt {x k : Nat} (h : 2 ^ k < x) :
    k < ceilLog2 x := by
  by_contra hnot
  have hceil_le : ceilLog2 x <= k := Nat.le_of_not_gt hnot
  have hx_le : x <= 2 ^ k :=
    (le_two_pow_ceilLog2 x).trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hceil_le)
  exact Nat.not_lt_of_ge hx_le h

/-- The diamond transform is unbounded. -/
theorem diamond_unbounded : forall t : Nat, exists r : Nat, t <= D.diamond r := by
  intro t
  induction t with
  | zero =>
      exact Exists.intro 0 (Nat.zero_le _)
  | succ t ih =>
      cases ih with
      | intro x hx =>
      cases D.unbounded (2 ^ x + 1) with
      | intro r hr =>
      have hpow_lt : 2 ^ x < D.g r := by omega
      have hr_large : 1 < D.g r := by
        have htwo_pos : 0 < 2 ^ x := by positivity
        omega
      have hx_le_log : x <= ceilLog2 (D.g r) :=
        Nat.le_of_lt (lt_ceilLog2_of_pow_lt hpow_lt)
      have hmono := D.diamond_monotone hx_le_log
      apply Exists.intro r
      rw [diamond_eq_large D hr_large]
      omega

end DiamondInput

end PathCompressionDigestion
