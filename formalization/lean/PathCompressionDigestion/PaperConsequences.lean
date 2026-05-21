import PathCompressionDigestion.ConcreteCore

/-!
# Direct paper-facing consequences

This file records the immediate concrete `J`-side consequence of the
ConcreteCore comparison:

`A z (4 * Q) > r -> J (z + 1) r <= Q`.
-/

namespace PathCompressionDigestion

/-- Any rank at most the concrete inverse stays below the threshold. -/
theorem J_le_of_le_R {k r t : Nat} (h : r <= R k t) :
    J k r <= t := by
  exact (J_monotone k h).trans (J_R_le k t)

/--
Direct paper-facing consequence of the concrete main comparison:
if `r` is below the Ackermann comparison bound, then the concrete `J` row
at level `z + 1` sends `r` below threshold `Q`.
-/
theorem direct_paper_consequence
    {z Q r : Nat}
    (hz : 1 <= z)
    (hQ : 1 <= Q)
    (hr : A z (4 * Q) > r) :
    J (z + 1) r <= Q := by
  have hcomparison : A z (4 * Q) <= R (z + 1) Q :=
    concrete_main_comparison z Q hz hQ
  have hrR : r <= R (z + 1) Q :=
    (Nat.le_of_lt hr).trans hcomparison
  exact J_le_of_le_R hrR

end PathCompressionDigestion
