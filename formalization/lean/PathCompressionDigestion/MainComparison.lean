import PathCompressionDigestion.Threshold

/-!
# Main abstract comparison

This file proves the final threshold comparison once the paper's threshold
engine and row-domination invariant are available as hypotheses. It is the
bounded formalization target for paper Theorem 4.7:

`R (z+1) Q >= A z (4*Q)` for `z >= 1` and `Q >= 1`.
-/

namespace PathCompressionDigestion

namespace Abstract

variable (R : ThresholdFamily)

/--
Additional comparison assumptions corresponding to paper Lemma 4.6 and to the
`Q = 1` case split in paper Theorem 4.7.
-/
structure MainComparisonAssumptions : Prop extends ThresholdAssumptions R where
  rowDominationInvariant :
    forall j x : Nat, 1 <= j -> 1 <= x -> A (j + 1) x <= R j x
  smallQOne :
    forall z : Nat, 1 <= z -> A z 4 <= R (z + 1) 1

variable {R}

/-- Paper Theorem 4.7, abstract threshold-comparison form. -/
theorem main_comparison (H : MainComparisonAssumptions R) :
    forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q := by
  intro z Q hz hQ
  cases one_or_two_le hQ with
  | inl hQeq =>
    subst Q
    simpa using H.smallQOne z hz
  | inr hQge =>
    have hx : 1 <= 4 * Q := one_le_four_mul hQ
    have hRowA : A z (4 * Q) <= A (z + 1) (4 * Q) :=
      Ackermann.row_domination hx
    have hDom : A (z + 1) (4 * Q) <= R z (4 * Q) :=
      H.rowDominationInvariant z (4 * Q) hz hx
    have hJump : R z (4 * Q) <= R (z + 1) Q :=
      H.thresholdJump z Q hQge
    exact hRowA.trans (hDom.trans hJump)

end Abstract

end PathCompressionDigestion
