import PathCompressionDigestion.AlphaPrelude
import PathCompressionDigestion.PaperConsequences

/-!
# Paper-specific alpha tail, first layer

This file instantiates the generic alpha prelude with the packet quantities

* `L(n) = ceil(log_2 max(n,2))`;
* `Q(m,n) = ceil(1 + m/n)`;
* `alphaQ`, using the packet Ackermann column `A z (4 * Q)`;
* `alphaJQ`, using the concrete threshold inverse `R` for the `J` hierarchy;
* `alphaJS`, using the integer threshold corresponding to the source real
  condition `J_k(L(n)) <= 1 + m/n`.

The source recurrence/cost theorem and the full real-threshold `+2` comparison
are intentionally not formalized here.
-/

namespace PathCompressionDigestion

/-- Natural ceiling division, used only for positive denominators in the packet `Q`. -/
def ceilDiv (m n : Nat) : Nat :=
  (m + n - 1) / n

/-- Packet rank cutoff: `L(n) = ceil(log_2 max(n,2))`. -/
def L (n : Nat) : Nat :=
  ceilLog2 (max n 2)

/-- Packet integer threshold: `Q(m,n) = ceil(1 + m/n)`. -/
def Q (m n : Nat) : Nat :=
  1 + ceilDiv m n

/--
Integer threshold corresponding to the source real condition
`J_k(L(n)) <= 1 + m/n` for positive `n`, since `J_k(L(n))` is Nat-valued.
-/
def sourceThreshold (m n : Nat) : Nat :=
  1 + m / n

/-- Ackermann family shifted so its indices are the paper's `z >= 1` indices. -/
def ackermannAlphaFamily : ThresholdFamily :=
  fun z threshold => A (z + 1) (4 * threshold)

/-- Paper packet inverse `alpha_Q(m,n)`, represented with `Abstract.alphaOf`. -/
noncomputable def alphaQ (m n : Nat) : Nat :=
  Abstract.alphaOf ackermannAlphaFamily (L n + 1) (Q m n) + 1

/-- Packet `J`-threshold inverse `alpha_J^Q(m,n)`. -/
noncomputable def alphaJQ (m n : Nat) : Nat :=
  Abstract.alphaOf R (L n) (Q m n)

/-- Source-faithful `J` threshold inverse `alpha_J^S(m,n)`, Nat-threshold encoded. -/
noncomputable def alphaJS (m n : Nat) : Nat :=
  Abstract.alphaOf R (L n) (sourceThreshold m n)

/-- Explicit witness condition for the minimum defining `alphaQ`. -/
def alphaQExists (m n : Nat) : Prop :=
  Exists fun z : Nat => L n + 1 <= ackermannAlphaFamily z (Q m n)

@[simp] theorem one_le_Q (m n : Nat) : 1 <= Q m n := by
  simp [Q]

theorem one_le_L (n : Nat) : 1 <= L n := by
  have htwo : 2 <= max n 2 := le_max_right n 2
  have hlog : ceilLog2 2 <= ceilLog2 (max n 2) :=
    monotone_ceilLog2 htwo
  simpa [L] using hlog

@[simp] theorem one_le_alphaQ (m n : Nat) : 1 <= alphaQ m n := by
  simp [alphaQ]

private theorem two_mul_le_A (i x : Nat) : 2 * x <= A i x := by
  cases i with
  | zero =>
      simp
  | succ i =>
      exact Ackermann.ge_two_mul_succ i x

private theorem one_le_A_four (i : Nat) : 1 <= A i 4 := by
  have h : 4 <= A i 4 := Ackermann.self_le i 4
  omega

private theorem ackermann_succ_four (i : Nat) :
    A (i + 1) 4 = A i (A i 4) := by
  calc
    A (i + 1) 4 = A i (A (i + 1) 3) := by
      rw [show 4 = 2 + 2 by norm_num, A_succ_succ]
    _ = A i (A i 4) := by
      have hthree : A (i + 1) 3 = A i 4 := by
        rw [show 3 = 1 + 2 by norm_num, A_succ_succ]
        simp [Ackermann.eval_two]
      rw [hthree]

private theorem ackermann_four_column_strict_step (i : Nat) :
    A i 4 + 1 <= A (i + 1) 4 := by
  rw [ackermann_succ_four]
  have htwo : 2 * A i 4 <= A i (A i 4) := two_mul_le_A i (A i 4)
  have hpos : 1 <= A i 4 := one_le_A_four i
  omega

private theorem ackermann_four_column_linear (t : Nat) :
    t <= A t 4 := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      exact (Nat.succ_le_succ ih).trans (ackermann_four_column_strict_step t)

theorem alphaQ_exists (m n : Nat) :
    alphaQExists m n := by
  refine ⟨L n, ?_⟩
  have hlinear : L n + 1 <= A (L n + 1) 4 :=
    ackermann_four_column_linear (L n + 1)
  have hmono : A (L n + 1) 4 <= A (L n + 1) (4 * Q m n) := by
    simpa using
      (Ackermann.four_mul_column_mono
        (z := L n + 1)
        (Q := 1)
        (Q' := Q m n)
        (one_le_Q m n))
  simpa [ackermannAlphaFamily] using hlinear.trans hmono

theorem sourceThreshold_le_Q_pos {m n : Nat} (hn : 0 < n) :
    sourceThreshold m n <= Q m n := by
  have hm_le : m <= m + n - 1 := by
    omega
  have hdiv : m / n <= (m + n - 1) / n :=
    Nat.div_le_div_right hm_le
  simpa [sourceThreshold, Q, ceilDiv] using Nat.succ_le_succ hdiv

theorem sourceThreshold_le_Q {m n : Nat} (hn : 1 <= n) :
    sourceThreshold m n <= Q m n :=
  sourceThreshold_le_Q_pos (m := m) (n := n) hn

theorem ceilDiv_eq_div_of_dvd_pos {m n : Nat} (hn : 0 < n) (hdiv : n ∣ m) :
    ceilDiv m n = m / n := by
  unfold ceilDiv
  apply Nat.div_eq_of_lt_le
  · have hmul : m / n * n = m := Nat.div_mul_cancel hdiv
    rw [hmul]
    omega
  · have hmul : m / n * n = m := Nat.div_mul_cancel hdiv
    rw [Nat.add_mul, Nat.one_mul, hmul]
    omega

theorem ceilDiv_eq_div_add_one_of_not_dvd_pos {m n : Nat}
    (hn : 0 < n) (hndiv : ¬ n ∣ m) :
    ceilDiv m n = m / n + 1 := by
  unfold ceilDiv
  apply Nat.div_eq_of_lt_le
  · have hlt : n * (m / n) < m :=
      Nat.mul_div_lt_iff_not_dvd.mpr hndiv
    rw [Nat.mul_comm n (m / n)] at hlt
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hdecomp : n * (m / n) + m % n = m := Nat.div_add_mod m n
    rw [Nat.mul_comm n (m / n)] at hdecomp
    have hmod_lt : m % n < n := Nat.mod_lt m hn
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

theorem sourceThreshold_eq_Q_of_dvd {m n : Nat} (hn : 0 < n) (hdiv : n ∣ m) :
    sourceThreshold m n = Q m n := by
  simp [sourceThreshold, Q, ceilDiv_eq_div_of_dvd_pos hn hdiv]

theorem Q_eq_sourceThreshold_add_one_of_not_dvd
    {m n : Nat} (hn : 0 < n) (hndiv : ¬ n ∣ m) :
    Q m n = sourceThreshold m n + 1 := by
  simp [sourceThreshold, Q, ceilDiv_eq_div_add_one_of_not_dvd_pos hn hndiv]
  omega

theorem Q_le_sourceThreshold_add_one_pos {m n : Nat} (hn : 0 < n) :
    Q m n <= sourceThreshold m n + 1 := by
  by_cases hdiv : n ∣ m
  · rw [← sourceThreshold_eq_Q_of_dvd (m := m) (n := n) hn hdiv]
    exact Nat.le_succ (sourceThreshold m n)
  · rw [Q_eq_sourceThreshold_add_one_of_not_dvd (m := m) (n := n) hn hdiv]

/-- `alphaQ` satisfies its Ackermann predicate whenever the defining set is nonempty. -/
theorem alphaQ_spec {m n : Nat} (h : alphaQExists m n) :
    L n < A (alphaQ m n) (4 * Q m n) := by
  have hspec :
      L n + 1 <=
        ackermannAlphaFamily
          (Abstract.alphaOf ackermannAlphaFamily (L n + 1) (Q m n))
          (Q m n) :=
    Abstract.alpha_spec
      (R := ackermannAlphaFamily)
      (target := L n + 1)
      (threshold := Q m n)
      h
  exact Nat.lt_of_succ_le (by
    simpa [alphaQ, ackermannAlphaFamily] using hspec)

/--
Concrete alpha bridge from any paper Ackermann witness. This is the direct
`alpha_J^Q <= z + 1` consequence of the already-proved concrete comparison.
-/
theorem alphaJQ_le_succ_of_ackermann_witness {m n z : Nat}
    (hz : 1 <= z)
    (hTarget : L n < A z (4 * Q m n)) :
    alphaJQ m n <= z + 1 := by
  exact
    Abstract.alphaOf_le_succ_of_le_ackermann_four_mul
      (R := R)
      (target := L n)
      (z := z)
      (Q := Q m n)
      (Nat.le_of_lt hTarget)
      (concrete_main_comparison z (Q m n) hz (one_le_Q m n))

/--
Conditional packet alpha comparison. The only explicit assumption is that the
minimum defining `alphaQ` has an Ackermann witness.
-/
theorem alphaJQ_le_alphaQ_add_one {m n : Nat} (h : alphaQExists m n) :
    alphaJQ m n <= alphaQ m n + 1 :=
  alphaJQ_le_succ_of_ackermann_witness
    (m := m)
    (n := n)
    (z := alphaQ m n)
    (one_le_alphaQ m n)
    (alphaQ_spec h)

/-- Unconditional packet alpha comparison, using existence of `alphaQ`. -/
theorem alphaJQ_le_alphaQ_add_one_unconditional (m n : Nat) :
    alphaJQ m n <= alphaQ m n + 1 := by
  exact alphaJQ_le_alphaQ_add_one (m := m) (n := n) (alphaQ_exists m n)

/-- If the source threshold equals the packet threshold, the two `J` alphas coincide. -/
theorem alphaJS_eq_alphaJQ_of_sourceThreshold_eq_Q {m n : Nat}
    (h : sourceThreshold m n = Q m n) :
    alphaJS m n = alphaJQ m n := by
  simp [alphaJS, alphaJQ, h]

/--
Integral-threshold bridge, conditional on the arithmetic equality between the
source and packet thresholds and on existence of the packet Ackermann witness.
-/
theorem alphaJS_le_alphaQ_add_one_of_sourceThreshold_eq_Q {m n : Nat}
    (hexists : alphaQExists m n)
    (hthreshold : sourceThreshold m n = Q m n) :
    alphaJS m n <= alphaQ m n + 1 := by
  rw [alphaJS_eq_alphaJQ_of_sourceThreshold_eq_Q hthreshold]
  exact alphaJQ_le_alphaQ_add_one hexists

end PathCompressionDigestion
