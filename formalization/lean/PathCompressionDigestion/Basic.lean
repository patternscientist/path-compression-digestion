import Mathlib.Tactic

/-!
# Basic utilities

Small shared facts for the path-compression digestion Lean scaffold.
The formalization lane is intentionally narrow: it supports the abstract
threshold comparison and does not define the Seidel--Sharir `J` hierarchy.
-/

namespace PathCompressionDigestion

theorem one_or_two_le {n : Nat} (h : 1 <= n) : n = 1 \/ 2 <= n := by
  omega

theorem one_le_four_mul {n : Nat} (h : 1 <= n) : 1 <= 4 * n := by
  omega

end PathCompressionDigestion
