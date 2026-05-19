import PathCompressionDigestion.Ackermann

/-!
# Abstract threshold engine

This file intentionally does not define `J`, `diamond`, or the concrete inverse
`R_k(t) = max { r >= 0 : J_k r <= t }`. Instead it packages the threshold facts
needed for the comparison theorem as assumptions on an abstract family
`R : Nat -> Nat -> Nat`.

The assumptions correspond to the threshold-inversion spine of the paper:

* exact base inverse: `R 0 t = 2*t + 1`;
* monotonicity of threshold inverses in the threshold parameter;
* monotonicity in the `J` level;
* threshold step, paper Lemma 4.3.

The threshold jump of paper Lemma 4.4 is derived below from these primitive
assumptions.
-/

namespace PathCompressionDigestion

abbrev ThresholdFamily := Nat -> Nat -> Nat

namespace Abstract

variable (R : ThresholdFamily)

/-- Paper Section 4.2 definition, represented abstractly. -/
def thresholdInverseShape : Prop :=
  True

/-- Primitive assumptions corresponding to paper Lemmas 4.2--4.3. -/
structure ThresholdCoreAssumptions : Prop where
  baseExact :
    forall t : Nat, R 0 t = 2 * t + 1
  monotoneThreshold :
    forall k : Nat, Monotone (R k)
  monotoneLevel :
    forall k t : Nat, R k t <= R (k + 1) t
  thresholdStep :
    forall k t : Nat, R k (2 ^ (R (k + 1) t)) <= R (k + 1) (t + 1)

/--
Compatibility wrapper for the original scaffold interface. New theorems should
prefer `ThresholdCoreAssumptions`; the jump field is derived below.
-/
structure ThresholdAssumptions : Prop extends ThresholdCoreAssumptions R where
  thresholdJump :
    forall k Q : Nat, 2 <= Q -> R k (4 * Q) <= R (k + 1) Q

variable {R}

/-- Level monotonicity iterated across an arbitrary level inequality. -/
theorem level_monotone_core (H : ThresholdCoreAssumptions R) {k l t : Nat} (hkl : k <= l) :
    R k t <= R l t := by
  induction l, hkl using Nat.le_induction with
  | base =>
      rfl
  | succ l _ ih =>
      exact ih.trans (H.monotoneLevel l t)

/-- Lower a threshold to level zero. -/
theorem threshold_lower_base (H : ThresholdCoreAssumptions R) (k t : Nat) :
    R 0 t <= R k t :=
  level_monotone_core (R := R) H (Nat.zero_le k)

/-- Every abstract threshold is at least `1`. -/
theorem one_le_threshold_core (H : ThresholdCoreAssumptions R) (k t : Nat) :
    1 <= R k t := by
  have hbase : 1 <= R 0 0 := by
    rw [H.baseExact 0]
  have hlevel : R 0 0 <= R k 0 :=
    threshold_lower_base (R := R) H k 0
  have hthreshold : R k 0 <= R k t :=
    H.monotoneThreshold k (Nat.zero_le t)
  exact hbase.trans (hlevel.trans hthreshold)

/-- Arithmetic bound used in paper Lemma 4.4. -/
theorem four_mul_le_two_pow_two_mul_sub_one {Q : Nat} (hQ : 2 <= Q) :
    4 * Q <= 2 ^ (2 * Q - 1) := by
  induction Q, hQ using Nat.le_induction with
  | base =>
      norm_num
  | succ Q hQ ih =>
      have hpow : 2 ^ (2 * (Q + 1) - 1) = 4 * 2 ^ (2 * Q - 1) := by
        have heq : 2 * (Q + 1) - 1 = (2 * Q - 1) + 2 := by
          omega
        rw [heq, pow_add]
        norm_num
        ring
      rw [hpow]
      nlinarith

/-- Paper Lemma 4.4: threshold jump derived from the threshold step. -/
theorem threshold_jump_from_step (H : ThresholdCoreAssumptions R) :
    forall k Q : Nat, 2 <= Q -> R k (4 * Q) <= R (k + 1) Q := by
  intro k Q hQ
  have hbase_exact : R 0 (Q - 1) = 2 * (Q - 1) + 1 :=
    H.baseExact (Q - 1)
  have hbase_lower : R 0 (Q - 1) <= R (k + 1) (Q - 1) :=
    threshold_lower_base (R := R) H (k + 1) (Q - 1)
  have hexp_lower : 2 * Q - 1 <= R (k + 1) (Q - 1) := by
    omega
  have hpowmono :
      2 ^ (2 * Q - 1) <= 2 ^ R (k + 1) (Q - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp_lower
  have hfour : 4 * Q <= 2 ^ R (k + 1) (Q - 1) :=
    (four_mul_le_two_pow_two_mul_sub_one hQ).trans hpowmono
  have hmono : R k (4 * Q) <= R k (2 ^ R (k + 1) (Q - 1)) :=
    H.monotoneThreshold k hfour
  have hstep : R k (2 ^ R (k + 1) (Q - 1)) <= R (k + 1) Q := by
    have hQsucc : Q - 1 + 1 = Q := by
      omega
    simpa [hQsucc] using H.thresholdStep k (Q - 1)
  exact hmono.trans hstep

theorem base_lower (H : ThresholdAssumptions R) (t : Nat) :
    2 * t + 1 <= R 0 t := by
  rw [H.baseExact]

theorem threshold_step (H : ThresholdAssumptions R) (k t : Nat) :
    R k (2 ^ (R (k + 1) t)) <= R (k + 1) (t + 1) :=
  H.thresholdStep k t

theorem threshold_jump (H : ThresholdAssumptions R) {k Q : Nat} (hQ : 2 <= Q) :
    R k (4 * Q) <= R (k + 1) Q :=
  H.thresholdJump k Q hQ

/-- Convert primitive assumptions into the compatibility wrapper. -/
def ThresholdAssumptions.ofCore (H : ThresholdCoreAssumptions R) :
    ThresholdAssumptions R :=
  { H with
    thresholdJump := threshold_jump_from_step (R := R) H }

end Abstract

end PathCompressionDigestion
