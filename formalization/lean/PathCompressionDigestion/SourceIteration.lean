import PathCompressionDigestion.SourceCost

/-!
# Iterating a source shifting interface

This file replaces direct use of the opaque `SourceRecurrence` interface in one
direction: a base source bound plus a level-by-level shifting lemma along the
concrete `J` hierarchy imply `SourceRecurrence`.

It does not formalize the underlying Seidel--Sharir path-compression model or
prove the combinatorial shifting lemma for that model.
-/

namespace PathCompressionDigestion

/-- A source-cost bound with coefficient `k` and row function `g`. -/
def SourceBound (F : SourceCostFamily) (k : Nat) (g : Nat -> Nat) : Prop :=
  forall {m n r : Nat},
    1 <= m -> 1 <= n ->
      F m n r <= k * m + 2 * n * g r

/--
One source shifting step for a packaged diamond input.

For the concrete hierarchy this is instantiated with `D = JInput k`, so the
target row is definitionally the next `J` row.
-/
def SourceShiftStep
    (F : SourceCostFamily)
    (k : Nat)
    (D : DiamondInput) : Prop :=
  SourceBound F k D.g -> SourceBound F (k + 1) D.diamond

/--
Pure iteration of the source shifting interface through the concrete `J`
hierarchy.
-/
theorem sourceBound_J_of_iterated_shifting
    {F : SourceCostFamily}
    (hbase : SourceBound F 0 (J 0))
    (hshift : forall k : Nat, SourceShiftStep F k (JInput k)) :
    forall k : Nat, SourceBound F k (J k) := by
  intro k
  induction k with
  | zero =>
      exact hbase
  | succ k ih =>
      have hprev : SourceBound F k (JInput k).g := by
        intro m n r hm hn
        exact ih (m := m) (n := n) (r := r) hm hn
      have hnext : SourceBound F (k + 1) (JInput k).diamond :=
        hshift k hprev
      intro m n r hm hn
      simpa [J_succ_row] using hnext (m := m) (n := n) (r := r) hm hn

/--
The old `SourceRecurrence` interface follows from a source base bound and the
iterated source shifting step.
-/
theorem sourceRecurrence_of_iterated_shifting
    {F : SourceCostFamily}
    (hbase : SourceBound F 0 (J 0))
    (hshift : forall k : Nat, SourceShiftStep F k (JInput k)) :
    SourceRecurrence F := by
  constructor
  intro k m n r _hk hm hn
  exact sourceBound_J_of_iterated_shifting hbase hshift k hm hn

end PathCompressionDigestion
