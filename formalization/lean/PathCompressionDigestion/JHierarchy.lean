import PathCompressionDigestion.JBase
import PathCompressionDigestion.Diamond

/-!
# Concrete `J_k` hierarchy

This file builds the recursive concrete hierarchy on top of the diamond
transform:

```text
J_0(r)     = J0(r)
J_{k+1}(r) = (J_k)^diamond(r)
```

It packages each row as a `DiamondInput`, so the preservation lemmas from
`Diamond.lean` can be reused directly.
-/

namespace PathCompressionDigestion

namespace DiamondInput

/-- The successor operation on packaged diamond inputs. -/
def next (D : DiamondInput) : DiamondInput where
  g := D.diamond
  zero_eq := D.diamond_zero
  monotone := D.diamond_monotone
  unbounded := D.diamond_unbounded
  lt_self_pos := fun hr => D.diamond_lt_self_pos hr

end DiamondInput

/-- The concrete base row `J0` is unbounded. -/
theorem J0_unbounded : forall t : Nat, exists r : Nat, t <= J0 r := by
  intro t
  refine Exists.intro (2 * t) ?_
  unfold J0
  have h : (2 * t) / 2 = t := by
    exact Nat.mul_div_right t (by norm_num : 0 < 2)
  rw [h]

/-- The concrete base row strictly descends below the identity on positive inputs. -/
theorem J0_lt_self_pos {r : Nat} (hr : 0 < r) : J0 r < r := by
  cases one_or_two_le hr with
  | inl h =>
      subst r
      norm_num [J0]
  | inr h =>
      exact J0_lt_self (by omega)

/-- The base row packaged as a diamond input. -/
def J0Input : DiamondInput where
  g := J0
  zero_eq := J0_zero
  monotone := J0_monotone
  unbounded := J0_unbounded
  lt_self_pos := fun hr => J0_lt_self_pos hr

/-- Recursive packaged concrete `J_k` hierarchy. -/
def JInput : Nat -> DiamondInput
  | 0 => J0Input
  | k + 1 => (JInput k).next

/-- Concrete `J_k` hierarchy, obtained by projecting the packaged row. -/
def J (k r : Nat) : Nat :=
  (JInput k).g r

@[simp] theorem J_zero_row (r : Nat) :
    J 0 r = J0 r := by
  rfl

theorem J_succ_row (k r : Nat) :
    J (k + 1) r = (JInput k).diamond r := by
  rfl

@[simp] theorem J_zero_arg (k : Nat) :
    J k 0 = 0 := by
  change (JInput k).g 0 = 0
  exact (JInput k).zero_eq

/-- Each concrete row is monotone in the rank argument. -/
theorem J_monotone (k : Nat) :
    Monotone (J k) := by
  intro r s hrs
  change (JInput k).g r <= (JInput k).g s
  exact (JInput k).monotone hrs

/-- Each concrete row is unbounded. -/
theorem J_unbounded (k : Nat) :
    forall t : Nat, exists r : Nat, t <= J k r := by
  intro t
  simpa [J] using (JInput k).unbounded t

/-- Each concrete row strictly descends below the identity on positive inputs. -/
theorem J_lt_self_pos (k : Nat) {r : Nat} :
    0 < r -> J k r < r := by
  intro hr
  change (JInput k).g r < r
  exact (JInput k).lt_self_pos hr

/-- Each concrete row is pointwise bounded by the identity. -/
theorem J_le_self (k r : Nat) :
    J k r <= r := by
  cases r with
  | zero =>
      rw [J_zero_arg]
  | succ r =>
      exact Nat.le_of_lt (J_lt_self_pos k (Nat.succ_pos r))

/-- Successor rows are pointwise bounded by predecessor rows. -/
theorem J_succ_le (k r : Nat) :
    J (k + 1) r <= J k r := by
  simpa [J_succ_row, J] using (JInput k).diamond_le_g r

/-- The concrete hierarchy is antitone in the row index. -/
theorem J_level_antitone {k l r : Nat} :
    k <= l -> J l r <= J k r := by
  intro h
  induction h with
  | refl =>
      exact le_rfl
  | step h ih =>
      exact (J_succ_le _ r).trans ih

/-- Every concrete `J` row has value one at rank two. -/
@[simp] theorem J_two_arg (k : Nat) :
    J k 2 = 1 := by
  induction k with
  | zero =>
      norm_num [J, JInput, J0Input, J0]
  | succ k ih =>
      have hk : (JInput k).g 2 = 1 := by
        simpa [J] using ih
      change (JInput k).diamond 2 = 1
      rw [(JInput k).diamond_eq_small (by omega)]
      exact hk

/-- Concrete `J` rows are positive on every rank at least two. -/
theorem J_pos_of_two_le (k : Nat) {r : Nat} (hr : 2 <= r) :
    0 < J k r := by
  have hmono : J k 2 <= J k r := J_monotone k hr
  have hone : 1 <= J k r := by
    simpa [J_two_arg] using hmono
  omega

/--
For a concrete `J` row, a large value cannot have the delayed-row pathology:
after cutting at `ceilLog2 (J k r)`, the residual rank is still at least two.
-/
theorem J_large_residual_two_le (k r : Nat) (hlarge : 1 < J k r) :
    2 <= r - ceilLog2 (J k r) - 1 := by
  let x := J k r
  let s := ceilLog2 x
  have hx2 : 2 <= x := by omega
  have hs_ge_one : 1 <= s := by
    have hmono : ceilLog2 2 <= ceilLog2 x := monotone_ceilLog2 hx2
    simpa [s] using hmono
  have hlog : s <= x - 1 := by
    simpa [s] using ceilLog2_le_pred hx2
  have hs_succ_le_x : s + 1 <= x := by omega
  have hx_le_J0_raw : J k r <= J 0 r :=
    J_level_antitone (k := 0) (l := k) (r := r) (Nat.zero_le k)
  have hx_le_J0 : x <= J0 r := by
    simpa [x, J_zero_row] using hx_le_J0_raw
  have hs_succ_le_J0 : s + 1 <= J0 r := hs_succ_le_x.trans hx_le_J0
  let a := s + 1
  have ha_le_J0 : a <= J0 r := by
    simpa [a] using hs_succ_le_J0
  have hnot : Not (r <= 2 * (a - 1) + 1) := by
    intro hr
    have hj0_le : J0 r <= a - 1 :=
      (J0_le_iff_le_two_mul_add_one r (a - 1)).2 hr
    omega
  have htwice : 2 * a <= r := by
    have hlt : 2 * (a - 1) + 1 < r := Nat.lt_of_not_ge hnot
    omega
  have hs3 : s + 3 <= r := by omega
  have hres : 2 <= r - s - 1 := by omega
  simpa [x, s] using hres

/--
Concrete `JInput` rows keep a positive top residual in the large-row case.
This is the row fact that the delayed `r - 3` audit witness violates.
-/
theorem JInput_top_residual_pos_of_large
    (k r : Nat) (hlarge : 1 < (JInput k).g r) :
    0 < (JInput k).g (r - ceilLog2 ((JInput k).g r) - 1) := by
  have hres :
      2 <= r - ceilLog2 (J k r) - 1 := by
    exact J_large_residual_two_le k r (by simpa [J] using hlarge)
  have hpos :
      0 < J k (r - ceilLog2 (J k r) - 1) :=
    J_pos_of_two_le k hres
  simpa [J] using hpos

end PathCompressionDigestion
