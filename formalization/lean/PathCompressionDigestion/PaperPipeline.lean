import PathCompressionDigestion.SourceCost

/-!
# Paper-facing pipeline wrappers

This file exposes the formalized direct-proof pipeline under paper-facing
names. The finite cost bound remains conditional on `SourceRecurrence`; this
module does not formalize the Seidel--Sharir source recurrence/model.
-/

namespace PathCompressionDigestion

/-- Paper-facing name for the concrete threshold comparison. -/
theorem paper_concrete_main_comparison
    (z Q : Nat)
    (hz : 1 <= z)
    (hQ : 1 <= Q) :
    A z (4 * Q) <= R (z + 1) Q :=
  concrete_main_comparison z Q hz hQ

/-- Paper-facing direct `J` bound from the concrete comparison. -/
theorem paper_direct_J_bound
    {z Q r : Nat}
    (hz : 1 <= z)
    (hQ : 1 <= Q)
    (hr : A z (4 * Q) > r) :
    J (z + 1) r <= Q :=
  direct_paper_consequence hz hQ hr

/-- Paper-facing packet alpha comparison. -/
theorem paper_alphaJQ_bound (m n : Nat) :
    alphaJQ m n <= alphaQ m n + 1 :=
  alphaJQ_le_alphaQ_add_one_unconditional m n

/-- Paper-facing source-threshold alpha comparison on the positive denominator domain. -/
theorem paper_alphaJS_bound {m n : Nat} (hn : 0 < n) :
    alphaJS m n <= alphaQ m n + 2 :=
  alphaJS_le_alphaQ_add_two hn

/--
Final finite paper-facing cost bound, conditional on the source recurrence
interface.
-/
theorem paper_finite_bound_of_source_recurrence
    {F : SourceCostFamily}
    (HF : SourceRecurrence F)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    F m n (L n) <= (alphaQ m n + 3) * m + 4 * n :=
  source_cost_bound_of_recurrence HF hm hn

end PathCompressionDigestion
