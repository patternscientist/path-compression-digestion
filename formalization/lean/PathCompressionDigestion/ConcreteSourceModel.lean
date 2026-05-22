import PathCompressionDigestion.SourceModel

/-!
# Concrete source-model skeleton

This module starts the concrete layer beneath `SourceModel`.

It defines finite Lean objects for ranked forests, top-down compression paths,
single compression steps, and finite compression executions.  The resulting
`topDownCost` is the finite supremum of the costs of valid executions in this
skeleton.

The Seidel--Sharir base and shift obligations are recorded below as named
`Prop` targets, not as assumptions and not as theorems.  In particular this
file does not prove the combinatorial shift lemma and does not instantiate
`SourceModel`.
-/

namespace PathCompressionDigestion

namespace ConcreteSourceModel

/-- A finite ranked forest candidate on `n` vertices with ranks bounded by `r`. -/
structure RawRankedForest (n r : Nat) where
  parent : Fin n -> Fin n
  rank : Fin n -> Fin (r + 1)
deriving DecidableEq, Fintype

namespace RawRankedForest

variable {n r : Nat}

/-- The natural-valued rank of a vertex. -/
def rankNat (F : RawRankedForest n r) (v : Fin n) : Nat :=
  (F.rank v).val

/-- A root is represented by a self-parent pointer. -/
def IsRoot (F : RawRankedForest n r) (v : Fin n) : Prop :=
  F.parent v = v

/-- A leaf has no strict child in the parent map. -/
def IsLeaf (F : RawRankedForest n r) (v : Fin n) : Prop :=
  forall w : Fin n, F.parent w = v -> w = v

/-- Iterated parent map, used to express ancestry without leaving finite types. -/
def parentIter (F : RawRankedForest n r) : Nat -> Fin n -> Fin n
  | 0, v => v
  | t + 1, v => parentIter F t (F.parent v)

/-- `a` is an ancestor of `v` if it is reached by iterating parent pointers. -/
def IsAncestor (F : RawRankedForest n r) (v a : Fin n) : Prop :=
  exists t : Nat, F.parentIter t v = a

/--
Rank validity for the forest skeleton: every non-root parent step strictly
increases rank.  This is the finite acyclicity/rank discipline used by the
future source-model proof.
-/
def IsRankValid (F : RawRankedForest n r) : Prop :=
  forall v : Fin n, F.parent v ≠ v -> F.rankNat v < F.rankNat (F.parent v)

end RawRankedForest

/--
A bounded raw path.  `len` is at most `n + 1`, and `node` stores enough slots
to address every possible position in such a path.  Validity below determines
which prefix is active.
-/
structure RawCompressionPath (n : Nat) where
  len : Fin (n + 2)
  node : Fin (n + 1) -> Fin n
  root : Fin n
deriving DecidableEq, Fintype

namespace RawCompressionPath

variable {n r : Nat}

/-- Cost of one compression path, counted as traversed edges. -/
def cost (P : RawCompressionPath n) : Nat :=
  P.len.val - 1

/-- Adjacent active path slots follow parent pointers upward. -/
def IsParentChain (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  forall i j : Fin (n + 1),
    i.val + 1 = j.val -> j.val < P.len.val -> F.parent (P.node i) = P.node j

/-- The last active path slot is the stored root. -/
def LastMatchesRoot (P : RawCompressionPath n) : Prop :=
  forall i : Fin (n + 1), i.val + 1 = P.len.val -> P.node i = P.root

/-- Vertices strictly before the root in the active path prefix. -/
def IsCompressedVertex (P : RawCompressionPath n) (v : Fin n) : Prop :=
  exists i : Fin (n + 1), i.val + 1 < P.len.val /\ P.node i = v

/-- A source-style compression path ending at a root of `F`. -/
def IsValidFor (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  F.IsRankValid /\
    2 <= P.len.val /\
    P.IsParentChain F /\
    P.LastMatchesRoot /\
    F.IsRoot P.root

end RawCompressionPath

/-- One raw top-down compression step, relating a before/after forest and path. -/
structure RawCompressionStep (n r : Nat) where
  before : RawRankedForest n r
  after : RawRankedForest n r
  path : RawCompressionPath n
deriving DecidableEq, Fintype

namespace RawCompressionStep

variable {n r : Nat}

/-- Cost of a single valid step candidate. -/
def cost (S : RawCompressionStep n r) : Nat :=
  S.path.cost

/--
Concrete step validity: the path is valid in the before-forest, ranks are
preserved, vertices before the root are rewired to the root, and all other
parents are unchanged.
-/
def IsValid (S : RawCompressionStep n r) : Prop :=
  S.path.IsValidFor S.before /\
    S.after.IsRankValid /\
    (forall v : Fin n, S.after.rank v = S.before.rank v) /\
    (forall v : Fin n, S.path.IsCompressedVertex v -> S.after.parent v = S.path.root) /\
    (forall v : Fin n, ¬ S.path.IsCompressedVertex v -> S.after.parent v = S.before.parent v)

end RawCompressionStep

/-- A finite execution with exactly `m` top-down compression slots. -/
structure RawCompressionExecution (m n r : Nat) where
  step : Fin m -> RawCompressionStep n r
deriving DecidableEq, Fintype

namespace RawCompressionExecution

variable {m n r : Nat}

/-- Valid executions have valid steps and consecutive before/after states. -/
def IsValid (E : RawCompressionExecution m n r) : Prop :=
  (forall i : Fin m, (E.step i).IsValid) /\
    (forall i j : Fin m,
      i.val + 1 = j.val -> (E.step i).after = (E.step j).before)

/-- Total execution cost, as the sum of the path costs of all compression slots. -/
def cost (E : RawCompressionExecution m n r) : Nat :=
  Finset.univ.sum fun i : Fin m => (E.step i).cost

end RawCompressionExecution

/--
Concrete top-down execution cost for the finite skeleton: the largest cost of
any valid `m`-step execution over `n` vertices with ranks bounded by `r`.

This is a concrete `SourceCostFamily`, but the source base and shift bounds for
it are deliberately not asserted in this module.
-/
noncomputable def topDownCost : SourceCostFamily :=
  fun m n r => by
    classical
    exact
    ((Finset.univ : Finset (RawCompressionExecution m n r)).filter
        fun E => E.IsValid).sup fun E => E.cost

/-- The concrete base-bound target that a future worker should prove. -/
def topDownBaseBoundTarget : Prop :=
  SourceBound topDownCost 0 (J 0)

/-- The concrete Seidel--Sharir shift target over this finite execution model. -/
def topDownShiftStepTarget (k : Nat) : Prop :=
  SourceShiftStep topDownCost k (JInput k)

/-- The full structured source-model target for this concrete cost family. -/
def topDownSourceModelTarget : Prop :=
  topDownBaseBoundTarget /\ forall k : Nat, topDownShiftStepTarget k

/--
If the two concrete source obligations above are proved, the existing bridge
would package them as a `SourceModel`.
-/
noncomputable def topDownSourceModelCandidate
    (hbase : topDownBaseBoundTarget)
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceModel where
  Cost := topDownCost
  base_bound := hbase
  shifting_step := hshift

end ConcreteSourceModel

end PathCompressionDigestion
