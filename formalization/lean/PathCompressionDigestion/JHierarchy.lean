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

end PathCompressionDigestion
