import PathCompressionDigestion.ThresholdInverse

/-!
# Extra generic threshold-inverse helpers

This file contains small generic facts for instantiating
`ThresholdInverse.Data` from a monotone, zero, unbounded natural-valued
function.  It deliberately stays independent of the concrete `J` hierarchy.
-/

namespace PathCompressionDigestion

namespace ThresholdInverse

/--
Non-strict eventual domination from monotonicity and unboundedness.

Once `f B` reaches threshold `t`, monotonicity keeps every later value above
that threshold.
-/
theorem eventually_ge_of_monotone_unbounded
    {f : Nat -> Nat}
    (hf_mono : Monotone f)
    (hf_unbounded : forall t : Nat, exists r : Nat, t <= f r) :
    forall t : Nat, exists B : Nat, forall r : Nat, B <= r -> t <= f r := by
  intro t
  cases hf_unbounded t with
  | intro B hB =>
      exact Exists.intro B (fun r hBr => Nat.le_trans hB (hf_mono hBr))

/--
Strict eventual domination from monotonicity and unboundedness.

Applying unboundedness at `t + 1` gives a point already strictly above `t`;
monotonicity then propagates strictness to all later indices.
-/
theorem eventually_gt_of_monotone_unbounded
    {f : Nat -> Nat}
    (hf_mono : Monotone f)
    (hf_unbounded : forall t : Nat, exists r : Nat, t <= f r) :
    forall t : Nat, exists B : Nat, forall r : Nat, B < r -> t < f r := by
  intro t
  cases hf_unbounded (t + 1) with
  | intro B hB =>
      refine Exists.intro B ?_
      intro r hBr
      have hB_strict : t < f B := by
        exact Nat.lt_of_succ_le (by simpa [Nat.succ_eq_add_one] using hB)
      exact lt_of_lt_of_le hB_strict (hf_mono (Nat.le_of_lt hBr))

namespace Data

/--
Build generic threshold-inverse data from the standard future concrete row
hypotheses: zero value, monotonicity, and unboundedness.
-/
def of_monotone_unbounded
    (f : Nat -> Nat)
    (hf_zero : f 0 = 0)
    (hf_mono : Monotone f)
    (hf_unbounded : forall t : Nat, exists r : Nat, t <= f r) :
    Data where
  f := f
  monotone := hf_mono
  zero_eq := hf_zero
  eventually_gt := eventually_gt_of_monotone_unbounded hf_mono hf_unbounded

end Data

/--
Pointwise comparison wrapper for threshold inverses built with
`Data.of_monotone_unbounded`.

If `g r <= f r` pointwise, then the inverse for `f` is bounded by the inverse
for `g`.
-/
theorem thresholdInverse_mono_function_of_monotone_unbounded
    {f g : Nat -> Nat}
    (hf_zero : f 0 = 0)
    (hf_mono : Monotone f)
    (hf_unbounded : forall t : Nat, exists r : Nat, t <= f r)
    (hg_zero : g 0 = 0)
    (hg_mono : Monotone g)
    (hg_unbounded : forall t : Nat, exists r : Nat, t <= g r)
    (hgf : forall r : Nat, g r <= f r) (t : Nat) :
    thresholdInverse (Data.of_monotone_unbounded f hf_zero hf_mono hf_unbounded) t
      <= thresholdInverse (Data.of_monotone_unbounded g hg_zero hg_mono hg_unbounded) t := by
  exact thresholdInverse_mono_function
    (D1 := Data.of_monotone_unbounded f hf_zero hf_mono hf_unbounded)
    (D2 := Data.of_monotone_unbounded g hg_zero hg_mono hg_unbounded)
    hgf t

/--
The successor of the threshold inverse has already escaped the threshold.
-/
theorem lt_apply_succ_thresholdInverse (D : Data) (t : Nat) :
    t < D.f (thresholdInverse D t + 1) := by
  by_contra hnot
  have hle : D.f (thresholdInverse D t + 1) <= t := Nat.le_of_not_gt hnot
  have hmax :
      thresholdInverse D t + 1 <= thresholdInverse D t :=
    le_thresholdInverse_of_apply_le (D := D) hle
  exact (Nat.not_succ_le_self (thresholdInverse D t))
    (by simpa [Nat.succ_eq_add_one] using hmax)

end ThresholdInverse

end PathCompressionDigestion
