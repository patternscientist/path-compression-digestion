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

theorem sourceThreshold_le_Q {m n : Nat} (hn : 1 <= n) :
    sourceThreshold m n <= Q m n := by
  have hm_le : m <= m + n - 1 := by
    omega
  have hdiv : m / n <= (m + n - 1) / n :=
    Nat.div_le_div_right hm_le
  simpa [sourceThreshold, Q, ceilDiv] using Nat.succ_le_succ hdiv

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
