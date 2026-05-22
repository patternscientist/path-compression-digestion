import PathCompressionDigestion.SourceIteration

/-!
# Structured source-model interface

This module packages the smallest source-facing data currently needed to
derive the existing `SourceRecurrence` interface: a base bound at `J_0` and a
source-correct shifting step from each `J_k` row to the next.

The fields are still obligations.  This module does not define the actual
top-down path-compression executions or prove Seidel--Sharir Lemma 5 from that
combinatorial model.
-/

namespace PathCompressionDigestion

/--
An abstract source model equipped with the base bound and shifting step needed
to iterate through the concrete `J` hierarchy.
-/
structure SourceModel where
  Cost : SourceCostFamily
  base_bound : SourceBound Cost 0 (J 0)
  shifting_step : forall k : Nat, SourceShiftStep Cost k (JInput k)

/--
Any source model with the packaged base and shifting obligations satisfies the
paper-facing source recurrence interface.
-/
theorem sourceRecurrence_of_shifting
    (M : SourceModel) :
    SourceRecurrence M.Cost :=
  sourceRecurrence_of_iterated_shifting M.base_bound M.shifting_step

/--
Finite packet-normalized cost bound for any source model satisfying the
packaged source base and shifting obligations.
-/
theorem source_model_cost_bound
    (M : SourceModel)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    M.Cost m n (L n) <= (alphaQ m n + 3) * m + 4 * n :=
  source_cost_bound_of_recurrence (sourceRecurrence_of_shifting M) hm hn

end PathCompressionDigestion
