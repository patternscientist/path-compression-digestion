import PathCompressionDigestion.SourceDissection

/-!
# Execution-level source projections

This module packages the local dissection/projection facts from
`SourceDissection` into execution-level accounting lemmas.

It still does not assert the Seidel--Sharir shift theorem.  The projected
objects here are per-step objects over the restricted bottom/top vertex types;
the remaining bridge is the execution/restriction commutation theorem that
turns those projected steps into valid source executions for the restricted
forests.
-/

namespace PathCompressionDigestion

namespace ConcreteSourceModel

namespace RawCompressionPath

namespace ProjectedPathSegment

variable {alpha : Type*} {parent : alpha -> alpha}

/-- Last slot of a nonempty projected path segment. -/
def lastIndex (S : ProjectedPathSegment alpha parent) (hlen : 0 < S.len) : Fin S.len :=
  { val := S.len - 1, isLt := by omega }

/-- A projected segment is root-like when its last vertex is a restricted root. -/
def IsRootPath (S : ProjectedPathSegment alpha parent) : Prop :=
  forall hlen : 0 < S.len, parent (S.node (S.lastIndex hlen)) = S.node (S.lastIndex hlen)

/-- A projected segment is nonroot-like when its last vertex is not a restricted root. -/
def IsNonrootPath (S : ProjectedPathSegment alpha parent) : Prop :=
  exists hlen : 0 < S.len,
    Not (parent (S.node (S.lastIndex hlen)) = S.node (S.lastIndex hlen))

/-- Negating projected nonrootness is the same as projected rootness. -/
theorem not_nonroot_iff_root (S : ProjectedPathSegment alpha parent) :
    Not S.IsNonrootPath <-> S.IsRootPath := by
  constructor
  case mp =>
    intro h hlen
    by_contra hneq
    exact h (Exists.intro hlen hneq)
  case mpr =>
    intro hroot hnonroot
    cases hnonroot with
    | intro hlen hneq => exact hneq (hroot hlen)

/-- Indicator for projected nonrootpaths. -/
noncomputable def nonrootIndicator (S : ProjectedPathSegment alpha parent) : Nat := by
  classical
  exact if S.IsNonrootPath then 1 else 0

/-- Projected nonroot indicators are Boolean-valued naturals. -/
theorem nonrootIndicator_le_one (S : ProjectedPathSegment alpha parent) :
    S.nonrootIndicator <= 1 := by
  classical
  unfold nonrootIndicator
  by_cases h : S.IsNonrootPath <;> simp [h]

end ProjectedPathSegment

namespace ProjectedCompressionStep

variable {alpha : Type*}

/-- Nonrootness of a projected step is nonrootness of its projected segment. -/
def IsNonrootPath (S : ProjectedCompressionStep alpha) : Prop :=
  S.path.IsNonrootPath

/-- Indicator for projected-step nonrootpaths. -/
noncomputable def nonrootIndicator (S : ProjectedCompressionStep alpha) : Nat :=
  S.path.nonrootIndicator

/-- Projected-step nonroot indicators are Boolean-valued naturals. -/
theorem nonrootIndicator_le_one (S : ProjectedCompressionStep alpha) :
    S.nonrootIndicator <= 1 :=
  S.path.nonrootIndicator_le_one

end ProjectedCompressionStep

/--
If a dissection cut has a nonempty top suffix, then the bottom projection ends
at the cut boundary and is a rootpath in the bottom restricted forest.
-/
theorem bottomProjectionSegment_isRootPath_of_top_nonempty
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (hcut_lt : cut < P.len.val) :
    (P.bottomProjectionSegment D hchain cut hcut).IsRootPath := by
  intro hlen
  apply Subtype.ext
  let i : Fin (P.bottomProjectionLength D cut hcut) :=
    (P.bottomProjectionSegment D hchain cut hcut).lastIndex hlen
  have hcut_pos : 0 < cut := by
    have hi_raw : i.val < P.bottomProjectionLength D cut hcut := i.isLt
    have hi : i.val < cut := by
      change i.val < P.bottomProjectionLength D cut hcut
      exact hi_raw
    omega
  let orig : Fin (n + 1) := P.bottomProjectionIndex D cut hcut i
  let j : Fin (n + 1) :=
    { val := cut,
      isLt := by
        have hlen_le : P.len.val <= n + 1 := Nat.le_of_lt_succ P.len.isLt
        omega }
  have hstep : orig.val + 1 = j.val := by
    have hi_val : i.val = cut - 1 := by
      simp [i, ProjectedPathSegment.lastIndex, bottomProjectionSegment,
        bottomProjectionLength]
    simp [orig, j, bottomProjectionIndex]
    omega
  have hparent : F.parent (P.node orig) = P.node j :=
    hchain orig j hstep hcut_lt
  have hj_top : D.IsTop (P.node j) := by
    exact hcut.2.2 j hcut_lt (by simp [j])
  have hparent_top : D.IsTop (F.parent (P.node orig)) := by
    simpa [hparent] using hj_top
  have hbottom_val :
      (D.bottomParent (P.bottomProjectionNode D cut hcut i)).1 =
        (P.bottomProjectionNode D cut hcut i).1 :=
    D.bottomParent_val_of_parent_top (P.bottomProjectionNode D cut hcut i) hparent_top
  exact hbottom_val

/-- Indicator form of `bottomProjectionSegment_isRootPath_of_top_nonempty`. -/
theorem bottomProjectionSegment_nonrootIndicator_eq_zero_of_top_nonempty
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (hcut_lt : cut < P.len.val) :
    (P.bottomProjectionSegment D hchain cut hcut).nonrootIndicator = 0 := by
  classical
  unfold ProjectedPathSegment.nonrootIndicator
  have hroot : (P.bottomProjectionSegment D hchain cut hcut).IsRootPath :=
    P.bottomProjectionSegment_isRootPath_of_top_nonempty D hchain cut hcut hcut_lt
  have hnot : Not (P.bottomProjectionSegment D hchain cut hcut).IsNonrootPath :=
    ((ProjectedPathSegment.not_nonroot_iff_root
      (P.bottomProjectionSegment D hchain cut hcut)).2 hroot)
  rw [if_neg hnot]

end RawCompressionPath

namespace RawCompressionStep

variable {n r : Nat}

/-- Indicator for source nonrootpaths. -/
noncomputable def nonrootIndicator (S : RawCompressionStep n r) : Nat := by
  classical
  exact if S.path.IsNonrootPath S.before then 1 else 0

/--
One-step projected cost accounting with the source nonrootpath indicator.
Rootpaths contribute zero source cost; nonrootpaths pay the one boundary charge.
-/
theorem cost_le_projectedSteps_cost_add_nonrootIndicator
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).cost + S.nonrootIndicator := by
  classical
  by_cases hnonroot : S.path.IsNonrootPath S.before
  case pos =>
    unfold nonrootIndicator
    rw [if_pos hnonroot]
    exact S.cost_le_projectedSteps_cost_add_one D hS cut hcut
  case neg =>
    have hroot : S.path.IsRootPath S.before := by
      unfold RawCompressionPath.IsRootPath RawRankedForest.IsRoot
      unfold RawCompressionPath.IsNonrootPath at hnonroot
      exact Decidable.not_not.mp hnonroot
    unfold cost RawCompressionPath.sourceCost nonrootIndicator
    rw [if_pos hroot]
    rw [if_neg hnonroot]
    omega

end RawCompressionStep

namespace RawCompressionExecution

variable {m n r : Nat}

/-- The charge-unit execution cost is the sum of the source costs of its steps. -/
theorem cost_eq_stepCostSum
    (E : RawCompressionExecution m n r) :
    E.cost = E.stepCostSum := by
  classical
  unfold cost stepCostSum ChargeUnit
  calc
    Fintype.card (Sigma fun i : Fin m => Fin (E.step i).cost)
        = Finset.sum (Finset.univ : Finset (Fin m))
            (fun i => Fintype.card (Fin (E.step i).cost)) := by
            exact @Fintype.card_sigma (Fin m) (fun i => Fin ((E.step i).cost)) _ _
    _ = Finset.sum (Finset.univ : Finset (Fin m))
            (fun i => (E.step i).cost) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact Fintype.card_fin ((E.step i).cost)

/-- Canonical dissection cut for the `i`th step, chosen from path contiguity. -/
noncomputable def dissectionCut
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (i : Fin m) : Nat :=
  Classical.choose ((E.step i).exists_path_dissection_cut (D i) (hsteps i))

/-- The canonical cut satisfies the dissection cut specification. -/
theorem dissectionCut_spec
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (i : Fin m) :
    (E.step i).path.HasDissectionCut (D i) (E.dissectionCut hsteps D i) :=
  Classical.choose_spec ((E.step i).exists_path_dissection_cut (D i) (hsteps i))

/-- Sum of the bottom projected costs for a chosen family of cuts. -/
noncomputable def bottomProjectedCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost

/-- Sum of the top projected costs for a chosen family of cuts. -/
noncomputable def topProjectedCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost

/-- The stepwise nonroot indicators sum to the execution nonroot count. -/
theorem nonrootIndicator_sum_eq_nonrootCount
    (E : RawCompressionExecution m n r) :
    Finset.sum (Finset.univ : Finset (Fin m))
        (fun i => (E.step i).nonrootIndicator) =
      E.nonrootCount := by
  classical
  unfold RawCompressionStep.nonrootIndicator nonrootCount
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

/--
Execution-level projected cost accounting for a chosen family of dissection
cuts.  This is the concrete finite analogue of the cost side of the main lemma
before quotienting the projected steps into restricted executions.
-/
theorem stepCostSum_le_projectedCostSums_add_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D cut hcut +
        E.topProjectedCostSum hsteps D cut hcut + E.nonrootCount := by
  classical
  unfold stepCostSum bottomProjectedCostSum topProjectedCostSum
  let A : Fin m -> Nat := fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost
  let B : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost
  let N : Fin m -> Nat := fun i => (E.step i).nonrootIndicator
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (E.step i).cost) <=
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i => A i + B i + N i) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      change (E.step i).cost <= A i + B i + N i
      exact (E.step i).cost_le_projectedSteps_cost_add_nonrootIndicator
        (D i) (hsteps i) (cut i) (hcut i))
  have hsplit :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => A i + B i + N i) =
        Finset.sum (Finset.univ : Finset (Fin m)) A +
          Finset.sum (Finset.univ : Finset (Fin m)) B + E.nonrootCount := by
    calc
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => A i + B i + N i)
          = Finset.sum (Finset.univ : Finset (Fin m)) (fun i => A i + B i) +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.sum (Finset.univ : Finset (Fin m)) A +
              Finset.sum (Finset.univ : Finset (Fin m)) B) +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.univ : Finset (Fin m)) A +
            Finset.sum (Finset.univ : Finset (Fin m)) B + E.nonrootCount := by
              rw [nonrootIndicator_sum_eq_nonrootCount E]
  exact le_trans hsum (le_of_eq hsplit)

/--
Execution-level projected cost accounting using the canonical cuts supplied by
path contiguity.
-/
theorem stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) + E.nonrootCount := by
  exact E.stepCostSum_le_projectedCostSums_add_nonrootCount hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Execution-level projected cost accounting stated for the charge-unit execution
cost used by `topDownCost`.
-/
theorem cost_le_canonicalProjectedCostSums_add_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) + E.nonrootCount := by
  rw [E.cost_eq_stepCostSum]
  exact E.stepCostSum_le_canonicalProjectedCostSums_add_nonrootCount hsteps D

end RawCompressionExecution

end ConcreteSourceModel

end PathCompressionDigestion
