import PathCompressionDigestion.AlphaTail

/-!
# Conditional source-cost consequence

This file isolates the source recurrence used for the paper-facing finite cost
bound. It does not formalize the Seidel--Sharir path-compression model or prove
the source recurrence itself.
-/

namespace PathCompressionDigestion

/-- Abstract source cost family, standing in for the source path-compression cost. -/
abbrev SourceCostFamily := Nat -> Nat -> Nat -> Nat

/--
Conditional interface for the source recurrence consequence.

The recurrence is an explicit assumption about a cost family `F`; no actual
path-compression model is defined here.
-/
structure SourceRecurrence (F : SourceCostFamily) : Prop where
  recurrence :
    forall {k m n r : Nat},
      1 <= k -> 1 <= m -> 1 <= n ->
        F m n r <= k * m + 2 * n * J k r

/-- Packet `Q` arithmetic used in the finite cost translation. -/
theorem two_mul_n_mul_Q_le_two_mul_m_add_four_mul_n
    {m n : Nat} (hn : 1 <= n) :
    2 * n * Q m n <= 2 * m + 4 * n := by
  have hQ : Q m n <= sourceThreshold m n + 1 :=
    Q_le_sourceThreshold_add_one_pos (m := m) (n := n) hn
  have hmul :
      2 * n * Q m n <= 2 * n * (sourceThreshold m n + 1) :=
    Nat.mul_le_mul_left (2 * n) hQ
  have hsource :
      2 * n * (sourceThreshold m n + 1) <= 2 * m + 4 * n := by
    have hdiv : n * (m / n) <= m := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m n
    calc
      2 * n * (sourceThreshold m n + 1)
          = 2 * n * ((1 + m / n) + 1) := by
            rfl
      _ = 2 * (n * (m / n)) + 4 * n := by
            ring
      _ <= 2 * m + 4 * n := by
            have htwice : 2 * (n * (m / n)) <= 2 * m :=
              Nat.mul_le_mul_left 2 hdiv
            nlinarith
  exact hmul.trans hsource

/--
Finite paper-facing cost theorem, conditional on the source recurrence
interface.
-/
theorem source_cost_bound_of_recurrence
    {F : SourceCostFamily}
    (HF : SourceRecurrence F)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    F m n (L n) <= (alphaQ m n + 3) * m + 4 * n := by
  have hA : L n < A (alphaQ m n) (4 * Q m n) :=
    alphaQ_spec (alphaQ_exists m n)
  have hJ : J (alphaQ m n + 1) (L n) <= Q m n :=
    direct_paper_consequence
      (z := alphaQ m n)
      (Q := Q m n)
      (r := L n)
      (one_le_alphaQ m n)
      (one_le_Q m n)
      hA
  have hk : 1 <= alphaQ m n + 1 := by
    omega
  have hrec :
      F m n (L n) <=
        (alphaQ m n + 1) * m + 2 * n * J (alphaQ m n + 1) (L n) :=
    HF.recurrence (k := alphaQ m n + 1) (m := m) (n := n) (r := L n)
      hk hm hn
  have hJterm :
      2 * n * J (alphaQ m n + 1) (L n) <= 2 * n * Q m n :=
    Nat.mul_le_mul_left (2 * n) hJ
  have hrecQ :
      F m n (L n) <= (alphaQ m n + 1) * m + 2 * n * Q m n :=
    hrec.trans (Nat.add_le_add_left hJterm ((alphaQ m n + 1) * m))
  have hQarith :
      2 * n * Q m n <= 2 * m + 4 * n :=
    two_mul_n_mul_Q_le_two_mul_m_add_four_mul_n (m := m) (n := n) hn
  have htail :
      (alphaQ m n + 1) * m + 2 * n * Q m n <=
        (alphaQ m n + 3) * m + 4 * n := by
    calc
      (alphaQ m n + 1) * m + 2 * n * Q m n
          <= (alphaQ m n + 1) * m + (2 * m + 4 * n) := by
            exact Nat.add_le_add_left hQarith ((alphaQ m n + 1) * m)
      _ = (alphaQ m n + 3) * m + 4 * n := by
            ring
  exact hrecQ.trans htail

end PathCompressionDigestion
