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

/-- If the exponent is positive, then `2 <= 2^n`. -/
theorem two_le_two_pow {n : Nat} (hn : 1 <= n) : 2 <= 2 ^ n := by
  have hpow : 2 ^ 1 <= 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
  simpa using hpow

/-- If the exponent is at least `3`, then `8 <= 2^n`. -/
theorem eight_le_two_pow {n : Nat} (hn : 3 <= n) : 8 <= 2 ^ n := by
  have hpow : 2 ^ 3 <= 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
  simpa using hpow

/-- One application of the threshold step gives `R_k(2) <= R_{k+1}(1)`. -/
theorem threshold_two_le_succ_one (H : ThresholdCoreAssumptions R) (k : Nat) :
    R k 2 <= R (k + 1) 1 := by
  have hpow : 2 <= 2 ^ R (k + 1) 0 :=
    two_le_two_pow (one_le_threshold_core (R := R) H (k + 1) 0)
  have hmono : R k 2 <= R k (2 ^ R (k + 1) 0) :=
    H.monotoneThreshold k hpow
  exact hmono.trans (H.thresholdStep k 0)

/-- Base case of the row-domination invariant: `R_1(x)` dominates `A_2(x)`. -/
theorem row_domination_base (H : ThresholdCoreAssumptions R) :
    forall x : Nat, 1 <= x -> A 2 x <= R 1 x := by
  intro x hx
  cases x with
  | zero =>
      omega
  | succ n =>
      induction n with
      | zero =>
          have hpow : 2 <= 2 ^ R 1 0 :=
            two_le_two_pow (one_le_threshold_core (R := R) H 1 0)
          have hmono : R 0 2 <= R 0 (2 ^ R 1 0) :=
            H.monotoneThreshold 0 hpow
          have hstep : R 0 (2 ^ R 1 0) <= R 1 1 :=
            H.thresholdStep 0 0
          have hR02 : R 0 2 = 5 := by
            rw [H.baseExact 2]
          change 2 <= R 1 1
          omega
      | succ n ih =>
          have hxpos : 1 <= n + 1 := by omega
          have hApos : 1 <= A 2 (n + 1) := by
            have h := Ackermann.ge_two_mul (i := 2) (x := n + 1) (by omega) hxpos
            omega
          have hpowmono : 2 ^ A 2 (n + 1) <= 2 ^ R 1 (n + 1) :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) (ih (by omega))
          have htoR0 : A 2 (n + 2) <= R 0 (2 ^ R 1 (n + 1)) := by
            rw [A_succ_succ]
            rw [Ackermann.one_eq_pow hApos]
            rw [H.baseExact (2 ^ R 1 (n + 1))]
            omega
          exact htoR0.trans (H.thresholdStep 0 (n + 1))

/-- Inductive step for the row-domination invariant. -/
theorem row_domination_step (H : ThresholdCoreAssumptions R) {j : Nat}
    (ih :
      forall x : Nat, 1 <= x -> A (j + 2) x <= R (j + 1) x) :
    forall x : Nat, 1 <= x -> A (j + 3) x <= R (j + 2) x := by
  intro x hx
  cases x with
  | zero =>
      omega
  | succ n =>
      induction n with
      | zero =>
          have hR01 : R 0 1 = 3 := by
            rw [H.baseExact 1]
          have hlevel : R 0 1 <= R (j + 2) 1 :=
            level_monotone_core (R := R) H (Nat.zero_le (j + 2))
          change 2 <= R (j + 2) 1
          omega
      | succ n ihx =>
          have hxpos : 1 <= n + 1 := by omega
          have hRpos : 1 <= R (j + 2) (n + 1) :=
            one_le_threshold_core (R := R) H (j + 2) (n + 1)
          have hselfpow : R (j + 2) (n + 1) <= 2 ^ R (j + 2) (n + 1) := by
            have hself := Ackermann.self_le 1 (R (j + 2) (n + 1))
            rw [Ackermann.one_eq_pow hRpos] at hself
            exact hself
          have harg : A (j + 3) (n + 1) <= 2 ^ R (j + 2) (n + 1) :=
            (ihx (by omega)).trans hselfpow
          have hpowpos : 1 <= 2 ^ R (j + 2) (n + 1) := by
            exact Nat.one_le_pow _ _ (by omega)
          have hAck :
              A (j + 2) (A (j + 3) (n + 1))
                <= A (j + 2) (2 ^ R (j + 2) (n + 1)) :=
            Ackermann.monotone_right (j + 2) harg
          have hOuter :
              A (j + 2) (2 ^ R (j + 2) (n + 1))
                <= R (j + 1) (2 ^ R (j + 2) (n + 1)) :=
            ih (2 ^ R (j + 2) (n + 1)) hpowpos
          rw [A_succ_succ]
          exact (hAck.trans hOuter).trans (H.thresholdStep (j + 1) (n + 1))

/-- Positive-level form of the row-domination invariant. -/
theorem row_domination_invariant_succ (H : ThresholdCoreAssumptions R) :
    forall j x : Nat, 1 <= x -> A (j + 2) x <= R (j + 1) x := by
  intro j
  induction j with
  | zero =>
      exact row_domination_base (R := R) H
  | succ j ih =>
      exact row_domination_step (R := R) H ih

/-- Paper Lemma 4.6: the abstract threshold engine dominates the Ackermann rows. -/
theorem row_domination_invariant_from_core (H : ThresholdCoreAssumptions R) :
    forall j x : Nat, 1 <= j -> 1 <= x -> A (j + 1) x <= R j x := by
  intro j x hj hx
  cases j with
  | zero =>
      omega
  | succ j =>
      simpa [Nat.add_assoc] using row_domination_invariant_succ (R := R) H j x hx

/-- Compatibility alias for paper Lemma 4.6 using the legacy wrapper. -/
theorem row_domination_invariant (H : ThresholdAssumptions R) :
    forall j x : Nat, 1 <= j -> 1 <= x -> A (j + 1) x <= R j x :=
  row_domination_invariant_from_core (R := R) H.toThresholdCoreAssumptions

/-- The `z = 1` part of the `Q = 1` main-comparison case. -/
theorem small_Q_one_base (H : ThresholdCoreAssumptions R) : A 1 4 <= R 2 1 := by
  have hR11_lower : 3 <= R 1 1 := by
    have hR01 : R 0 1 = 3 := by
      rw [H.baseExact 1]
    have hlevel : R 0 1 <= R 1 1 :=
      H.monotoneLevel 0 1
    omega
  have hpow8 : 8 <= 2 ^ R 1 1 :=
    eight_le_two_pow hR11_lower
  have hmono0 : R 0 8 <= R 0 (2 ^ R 1 1) :=
    H.monotoneThreshold 0 hpow8
  have hstep01 : R 0 (2 ^ R 1 1) <= R 1 2 :=
    H.thresholdStep 0 1
  have hR08 : R 0 8 = 17 := by
    rw [H.baseExact 8]
  have hR12_lower : 17 <= R 1 2 := by
    omega
  have hR12_to_R21 : R 1 2 <= R 2 1 :=
    threshold_two_le_succ_one (R := R) H 1
  have hA14 : A 1 4 = 16 := by
    rw [Ackermann.one_eq_pow (by norm_num : 1 <= 4)]
    norm_num
  omega

/-- The `Q = 1` case split from paper Theorem 4.7. -/
theorem small_Q_one_from_core (H : ThresholdCoreAssumptions R) :
    forall z : Nat, 1 <= z -> A z 4 <= R (z + 1) 1 := by
  intro z hz
  cases z with
  | zero =>
      omega
  | succ z =>
      cases z with
      | zero =>
          simpa using small_Q_one_base (R := R) H
      | succ z =>
          have htwo : R (z + 2) 2 <= R (z + 3) 1 :=
            threshold_two_le_succ_one (R := R) H (z + 2)
          have hjump : R (z + 1) 8 <= R (z + 2) 2 := by
            simpa using threshold_jump_from_step (R := R) H (z + 1) 2 (by norm_num : 2 <= 2)
          have hx8 : 1 <= 8 := by norm_num
          have hrow : A (z + 2) 8 <= R (z + 1) 8 :=
            row_domination_invariant_from_core (R := R) H (z + 1) 8 (by omega) hx8
          have hAmono : A (z + 2) 4 <= A (z + 2) 8 :=
            Ackermann.monotone_right (z + 2) (by norm_num : 4 <= 8)
          exact hAmono.trans (hrow.trans (hjump.trans htwo))

/-- Compatibility alias for the `Q = 1` case using the legacy wrapper. -/
theorem small_Q_one (H : ThresholdAssumptions R) :
    forall z : Nat, 1 <= z -> A z 4 <= R (z + 1) 1 :=
  small_Q_one_from_core (R := R) H.toThresholdCoreAssumptions

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

/-- Paper Theorem 4.7 from the abstract threshold assumptions alone. -/
theorem main_comparison_from_threshold (H : ThresholdAssumptions R) :
    forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q := by
  let Hmain : MainComparisonAssumptions R :=
    { H with
      rowDominationInvariant := row_domination_invariant (R := R) H
      smallQOne := small_Q_one (R := R) H }
  exact main_comparison (R := R) Hmain

/-- Paper Theorem 4.7 from the primitive threshold assumptions alone. -/
theorem main_comparison_from_core (H : ThresholdCoreAssumptions R) :
    forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q :=
  main_comparison_from_threshold (R := R) (ThresholdAssumptions.ofCore (R := R) H)

end Abstract

end PathCompressionDigestion
