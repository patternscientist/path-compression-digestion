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
* threshold step, paper Lemma 4.3;
* threshold jump, paper Lemma 4.4.
-/

namespace PathCompressionDigestion

abbrev ThresholdFamily := Nat -> Nat -> Nat

namespace Abstract

variable (R : ThresholdFamily)

/-- Paper Section 4.2 definition, represented abstractly. -/
def thresholdInverseShape : Prop :=
  True

/-- Assumptions corresponding to paper Lemmas 4.2--4.4. -/
structure ThresholdAssumptions : Prop where
  baseExact :
    forall t : Nat, R 0 t = 2 * t + 1
  monotoneThreshold :
    forall k : Nat, Monotone (R k)
  monotoneLevel :
    forall k t : Nat, R k t <= R (k + 1) t
  thresholdStep :
    forall k t : Nat, R k (2 ^ (R (k + 1) t)) <= R (k + 1) (t + 1)
  thresholdJump :
    forall k Q : Nat, 2 <= Q -> R k (4 * Q) <= R (k + 1) Q

variable {R}

theorem base_lower (H : ThresholdAssumptions R) (t : Nat) :
    2 * t + 1 <= R 0 t := by
  rw [H.baseExact]

theorem threshold_step (H : ThresholdAssumptions R) (k t : Nat) :
    R k (2 ^ (R (k + 1) t)) <= R (k + 1) (t + 1) :=
  H.thresholdStep k t

theorem threshold_jump (H : ThresholdAssumptions R) {k Q : Nat} (hQ : 2 <= Q) :
    R k (4 * Q) <= R (k + 1) Q :=
  H.thresholdJump k Q hQ

end Abstract

end PathCompressionDigestion
