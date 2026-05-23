import PathCompressionDigestion.SourceModel

/-!
# Concrete source-model skeleton

This module starts the concrete layer beneath `SourceModel`.

It defines finite Lean objects for ranked forests, source-style top-down
compression paths, single compression steps, finite compression executions, and
base-case rank-accounting certificates. The resulting `topDownCost` is the
finite supremum of the costs of valid, base-accounted executions in this
skeleton.

The source base obligation is proved for this base-accounted cost family. The
remaining gap is to derive the rank-accounting certificates from the raw
compression-step semantics, and then to prove the Seidel--Sharir shift lemma.
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
increases rank. This is the finite acyclicity/rank discipline used by the
future source-model proof.
-/
def IsRankValid (F : RawRankedForest n r) : Prop :=
  forall v : Fin n, Not (F.parent v = v) -> F.rankNat v < F.rankNat (F.parent v)

end RawRankedForest

/--
A bounded raw path. `len` is at most `n + 1`, and `node` stores enough slots to
address every possible position in such a path. Validity below determines which
prefix is active.
-/
structure RawCompressionPath (n : Nat) where
  len : Fin (n + 2)
  node : Fin (n + 1) -> Fin n
  target : Fin n
deriving DecidableEq, Fintype

namespace RawCompressionPath

variable {n r : Nat}

/-- Raw edge count of one compression path. -/
def cost (P : RawCompressionPath n) : Nat :=
  P.len.val - 1

/-- Adjacent active path slots follow parent pointers upward. -/
def IsParentChain (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  forall i j : Fin (n + 1),
    i.val + 1 = j.val -> j.val < P.len.val -> F.parent (P.node i) = P.node j

/-- The last active path slot is the stored target ancestor. -/
def LastMatchesTarget (P : RawCompressionPath n) : Prop :=
  forall i : Fin (n + 1), i.val + 1 = P.len.val -> P.node i = P.target

/-- Vertices strictly before the target in the active path prefix. -/
def IsCompressedVertex (P : RawCompressionPath n) (v : Fin n) : Prop :=
  exists i : Fin (n + 1), i.val + 1 < P.len.val /\ P.node i = v

/-- A source rootpath is a path whose target ancestor is a root. -/
def IsRootPath (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  F.IsRoot P.target

/-- A source nonrootpath is a path whose target ancestor is not a root. -/
def IsNonrootPath (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  Not (F.parent P.target = P.target)

/--
Source-style path cost. Rootpaths are charged zero; nonrootpaths are charged
the number of active vertices strictly before the target ancestor.
-/
noncomputable def sourceCost (F : RawRankedForest n r) (P : RawCompressionPath n) : Nat := by
  classical
  exact if P.IsRootPath F then 0 else P.cost

/-- A source-style compression path ending at an ancestor of its first vertex. -/
def IsValidFor (F : RawRankedForest n r) (P : RawCompressionPath n) : Prop :=
  F.IsRankValid /\
    2 <= P.len.val /\
    P.IsParentChain F /\
    P.LastMatchesTarget

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
noncomputable def cost (S : RawCompressionStep n r) : Nat :=
  S.path.sourceCost S.before

/--
Concrete step validity: the path is valid in the before-forest, ranks are
preserved, nonrootpath vertices before the target are rewired to the target's
old parent, rootpaths are left unchanged, and all other parents are unchanged.
-/
def IsValid (S : RawCompressionStep n r) : Prop :=
  S.path.IsValidFor S.before /\
    S.after.IsRankValid /\
    (forall v : Fin n, S.after.rank v = S.before.rank v) /\
    (S.path.IsRootPath S.before -> S.after.parent = S.before.parent) /\
    (S.path.IsNonrootPath S.before ->
      forall v : Fin n,
        S.path.IsCompressedVertex v -> S.after.parent v = S.before.parent S.path.target) /\
    (forall v : Fin n, Not (S.path.IsCompressedVertex v) -> S.after.parent v = S.before.parent v)

end RawCompressionStep

/-- A finite execution with exactly `m` top-down compression slots. -/
structure RawCompressionExecution (m n r : Nat) where
  step : Fin m -> RawCompressionStep n r
deriving DecidableEq, Fintype

namespace RawCompressionExecution

variable {m n r : Nat}

/-- The finite type of individual charged units in an execution. -/
def ChargeUnit (E : RawCompressionExecution m n r) : Type :=
  Sigma fun i : Fin m => Fin ((E.step i).cost)

noncomputable instance chargeUnitFintype (E : RawCompressionExecution m n r) :
    Fintype E.ChargeUnit := by
  unfold ChargeUnit
  infer_instance

/--
Base-case rank accounting certificate. Each charged unit is assigned
injectively to a vertex and one of that vertex's possible parent-rank increases
below the global bound `r`.
-/
def HasBaseRankAccounting (E : RawCompressionExecution m n r) : Prop :=
  Exists fun charge : E.ChargeUnit -> Prod (Fin n) (Fin (r - 1)) =>
    Function.Injective charge

/-- Every slot of an execution is a valid concrete compression step. -/
def HasValidSteps (E : RawCompressionExecution m n r) : Prop :=
  forall i : Fin m, (E.step i).IsValid

/-- Consecutive execution slots agree literally as before/after forests. -/
def HasConsecutiveStates (E : RawCompressionExecution m n r) : Prop :=
  forall i j : Fin m,
    i.val + 1 = j.val -> (E.step i).after = (E.step j).before

/--
Semantic execution validity, separated from the base/rank accounting
certificate used by the base-bound proof.
-/
def IsSemanticallyValid (E : RawCompressionExecution m n r) : Prop :=
  E.HasValidSteps /\ E.HasConsecutiveStates

/-- Valid executions have semantic validity and base accounting. -/
def IsValid (E : RawCompressionExecution m n r) : Prop :=
  E.HasValidSteps /\
    E.HasConsecutiveStates /\
    E.HasBaseRankAccounting

/-- The old execution validity predicate factors into semantic validity plus accounting. -/
theorem isValid_iff_semantic_and_rank
    (E : RawCompressionExecution m n r) :
    E.IsValid <-> E.IsSemanticallyValid /\ E.HasBaseRankAccounting := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩

/-- Valid executions are semantically valid. -/
theorem isSemanticallyValid_of_isValid
    (E : RawCompressionExecution m n r)
    (h : E.IsValid) :
    E.IsSemanticallyValid :=
  (E.isValid_iff_semantic_and_rank).1 h |>.1

/-- Valid executions carry the base/rank accounting certificate. -/
theorem hasBaseRankAccounting_of_isValid
    (E : RawCompressionExecution m n r)
    (h : E.IsValid) :
    E.HasBaseRankAccounting :=
  (E.isValid_iff_semantic_and_rank).1 h |>.2

/-- Semantic validity plus base/rank accounting reconstructs the old validity predicate. -/
theorem isValid_of_semantic_and_rank
    (E : RawCompressionExecution m n r)
    (hsemantic : E.IsSemanticallyValid)
    (hrank : E.HasBaseRankAccounting) :
    E.IsValid :=
  (E.isValid_iff_semantic_and_rank).2 ⟨hsemantic, hrank⟩

/--
Total execution cost, represented as the number of individual charged units
over all compression slots.
-/
noncomputable def cost (E : RawCompressionExecution m n r) : Nat :=
  Fintype.card E.ChargeUnit

/-- The rank-accounting certificate bounds the total charged cost. -/
theorem cost_le_base_budget
    (E : RawCompressionExecution m n r)
    (h : E.HasBaseRankAccounting) :
    E.cost <= n * (r - 1) := by
  classical
  cases h with
  | intro charge hcharge =>
      have hcard :
          E.cost <= Fintype.card (Prod (Fin n) (Fin (r - 1))) := by
        unfold cost
        exact Fintype.card_le_of_injective charge hcharge
      have hcodomain :
          Fintype.card (Prod (Fin n) (Fin (r - 1))) = n * (r - 1) := by
        simp
      rw [hcodomain] at hcard
      exact hcard

end RawCompressionExecution

/--
Concrete top-down execution cost for the finite skeleton: the largest cost of
any valid, base-accounted `m`-step execution over `n` vertices with ranks
bounded by `r`.

This is a concrete `SourceCostFamily`. The base bound below is proved from the
rank-accounting certificate in `RawCompressionExecution.IsValid`; deriving that
certificate from the raw step semantics remains future work.
-/
noncomputable def topDownCost : SourceCostFamily :=
  fun m n r => by
    classical
    exact
    ((Finset.univ : Finset (RawCompressionExecution m n r)).filter
        fun E => E.IsValid).sup fun E => E.cost

/-- Any valid concrete execution is bounded by the extremal `topDownCost`. -/
theorem RawCompressionExecution.cost_le_topDownCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid) :
    E.cost <= topDownCost m n r := by
  classical
  unfold topDownCost
  exact Finset.le_sup
    (s := (Finset.univ : Finset (RawCompressionExecution m n r)).filter
      fun E => E.IsValid)
    (f := fun E => E.cost)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ E, hE⟩)

/-- To bound `topDownCost`, it suffices to bound every valid execution. -/
theorem topDownCost_le_of_forall_valid
    {m n r B : Nat}
    (h : forall E : RawCompressionExecution m n r, E.IsValid -> E.cost <= B) :
    topDownCost m n r <= B := by
  classical
  unfold topDownCost
  refine Finset.sup_le ?_
  intro E hE
  exact h E (Finset.mem_filter.mp hE).2

/-- Every valid, base-accounted execution satisfies the source base budget. -/
theorem topDownCost_le_base_budget (m n r : Nat) :
    topDownCost m n r <= n * (r - 1) := by
  classical
  apply topDownCost_le_of_forall_valid
  intro E hvalid
  exact E.cost_le_base_budget (E.hasBaseRankAccounting_of_isValid hvalid)

private theorem pred_le_two_mul_J0 (r : Nat) :
    r - 1 <= 2 * J 0 r := by
  have h : r <= 2 * (r / 2) + 1 := by
    exact (J0_le_iff_le_two_mul_add_one r (r / 2)).1 le_rfl
  have hpred : r - 1 <= 2 * (r / 2) := by
    omega
  simpa [J_zero_row, J0] using hpred

/-- The concrete base-bound target for the base-accounted top-down cost. -/
def topDownBaseBoundTarget : Prop :=
  SourceBound topDownCost 0 (J 0)

/-- Source base obligation for the base-accounted concrete cost family. -/
theorem topDown_base_bound :
    topDownBaseBoundTarget := by
  intro m n r _hm _hn
  have hbudget : topDownCost m n r <= n * (r - 1) :=
    topDownCost_le_base_budget m n r
  have hpred : r - 1 <= 2 * J 0 r := pred_le_two_mul_J0 r
  have htarget : n * (r - 1) <= 0 * m + 2 * n * J 0 r := by
    calc
      n * (r - 1) <= n * (2 * J 0 r) := Nat.mul_le_mul_left n hpred
      _ = 0 * m + 2 * n * J 0 r := by
        ring
  exact hbudget.trans htarget

/--
Direct form of the base source obligation for the concrete cost family.

This is the Ambition-B theorem: the base `J_0` source bound is now a theorem
for `topDownCost`, not a field supplied by `SourceModel`.
-/
theorem topDown_base_sourceBound :
    SourceBound topDownCost 0 (J 0) :=
  topDown_base_bound

/-- The concrete Seidel--Sharir shift target over this finite execution model. -/
def topDownShiftStepTarget (k : Nat) : Prop :=
  SourceShiftStep topDownCost k (JInput k)

/-- The full structured source-model target for this concrete cost family. -/
def topDownSourceModelTarget : Prop :=
  topDownBaseBoundTarget /\ forall k : Nat, topDownShiftStepTarget k

/--
If the concrete source shift obligation is proved, the existing bridge would
package the base theorem and those shifts as a `SourceModel`.
-/
noncomputable def topDownSourceModelCandidate
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceModel where
  Cost := topDownCost
  base_bound := topDown_base_bound
  shifting_step := hshift

/--
Conditional packaging theorem: once the concrete shift theorem is proved, the
base theorem above supplies the remaining `SourceModel` field.
-/
noncomputable def topDown_sourceModel_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceModel :=
  topDownSourceModelCandidate hshift

/--
Conditional source recurrence for `topDownCost`, with the only remaining
assumption being the concrete Seidel--Sharir shift theorem.
-/
theorem sourceRecurrence_topDownCost_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k) :
    SourceRecurrence topDownCost :=
  by
    simpa [topDown_sourceModel_of_shift, topDownSourceModelCandidate] using
      sourceRecurrence_of_shifting (topDown_sourceModel_of_shift hshift)

/--
Conditional paper-facing finite bound for `topDownCost`, again isolated to the
single missing shift theorem.
-/
theorem paper_finite_bound_topDownCost_of_shift
    (hshift : forall k : Nat, topDownShiftStepTarget k)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    topDownCost m n (L n) <= (alphaQ m n + 3) * m + 4 * n :=
  source_cost_bound_of_recurrence
    (sourceRecurrence_topDownCost_of_shift hshift)
    hm hn

end ConcreteSourceModel

end PathCompressionDigestion
