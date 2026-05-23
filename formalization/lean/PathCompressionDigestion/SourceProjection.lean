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

/-- Root projected paths have zero nonroot indicator. -/
theorem nonrootIndicator_eq_zero_of_root
    (S : ProjectedPathSegment alpha parent)
    (hroot : S.IsRootPath) :
    S.nonrootIndicator = 0 := by
  classical
  unfold nonrootIndicator
  have hnot : Not S.IsNonrootPath :=
    (S.not_nonroot_iff_root).2 hroot
  rw [if_neg hnot]

/-- Empty projected paths have zero nonroot indicator. -/
theorem nonrootIndicator_eq_zero_of_len_eq_zero
    (S : ProjectedPathSegment alpha parent)
    (hlen : S.len = 0) :
    S.nonrootIndicator = 0 := by
  classical
  unfold nonrootIndicator IsNonrootPath
  rw [if_neg]
  intro hnonroot
  cases hnonroot with
  | intro hpos _hneq => omega

/-- Nonroot projected paths have nonroot indicator one. -/
theorem nonrootIndicator_eq_one_of_nonroot
    (S : ProjectedPathSegment alpha parent)
    (hnonroot : S.IsNonrootPath) :
    S.nonrootIndicator = 1 := by
  classical
  unfold nonrootIndicator
  rw [if_pos hnonroot]

end ProjectedPathSegment

namespace ProjectedCompressionStep

variable {alpha : Type*}

/-- A projected step is root-like when its projected segment ends at a restricted root. -/
def IsRootLike (S : ProjectedCompressionStep alpha) : Prop :=
  S.path.IsRootPath

/-- Nonrootness of a projected step is nonrootness of its projected segment. -/
def IsNonrootPath (S : ProjectedCompressionStep alpha) : Prop :=
  S.path.IsNonrootPath

/-- A projected step is charged precisely when it is nonroot-like. -/
def IsCharged (S : ProjectedCompressionStep alpha) : Prop :=
  S.IsNonrootPath

/-- Indicator for projected-step nonrootpaths. -/
noncomputable def nonrootIndicator (S : ProjectedCompressionStep alpha) : Nat :=
  S.path.nonrootIndicator

/-- Boundary charge carried by a projected step in the projected accounting API. -/
noncomputable def boundaryCharge (S : ProjectedCompressionStep alpha) : Nat :=
  S.nonrootIndicator

/-- Cost of the part of a projected step that is nonroot-like and recurrence-consumable. -/
noncomputable def consumableCost (S : ProjectedCompressionStep alpha) : Nat := by
  classical
  exact if S.IsCharged then S.cost else 0

/-- Cost of the root-like projected part that must be handled outside `topDownCost`. -/
noncomputable def exceptionalCost (S : ProjectedCompressionStep alpha) : Nat := by
  classical
  exact if S.IsCharged then 0 else S.cost

/-- Projected charged steps are exactly the non-root-like steps. -/
theorem not_charged_iff_rootLike (S : ProjectedCompressionStep alpha) :
    Not S.IsCharged <-> S.IsRootLike := by
  exact S.path.not_nonroot_iff_root

/-- Projected-step nonroot indicators are Boolean-valued naturals. -/
theorem nonrootIndicator_le_one (S : ProjectedCompressionStep alpha) :
    S.nonrootIndicator <= 1 :=
  S.path.nonrootIndicator_le_one

/-- Projected-step boundary charges are Boolean-valued naturals. -/
theorem boundaryCharge_le_one (S : ProjectedCompressionStep alpha) :
    S.boundaryCharge <= 1 := by
  exact S.nonrootIndicator_le_one

@[simp]
theorem consumableCost_eq_cost_of_charged
    (S : ProjectedCompressionStep alpha)
    (h : S.IsCharged) :
    S.consumableCost = S.cost := by
  simp [consumableCost, h]

@[simp]
theorem consumableCost_eq_zero_of_not_charged
    (S : ProjectedCompressionStep alpha)
    (h : Not S.IsCharged) :
    S.consumableCost = 0 := by
  simp [consumableCost, h]

@[simp]
theorem exceptionalCost_eq_zero_of_charged
    (S : ProjectedCompressionStep alpha)
    (h : S.IsCharged) :
    S.exceptionalCost = 0 := by
  simp [exceptionalCost, h]

@[simp]
theorem exceptionalCost_eq_cost_of_not_charged
    (S : ProjectedCompressionStep alpha)
    (h : Not S.IsCharged) :
    S.exceptionalCost = S.cost := by
  simp [exceptionalCost, h]

/-- Projected step cost splits into recurrence-consumable and exceptional parts. -/
theorem cost_eq_consumableCost_add_exceptionalCost
    (S : ProjectedCompressionStep alpha) :
    S.cost = S.consumableCost + S.exceptionalCost := by
  classical
  by_cases h : S.IsCharged <;> simp [consumableCost, exceptionalCost, h]

variable {beta : Type*}

/--
An equivalence between two projected step vertex types commutes with the
after-parent of the first step and the before-parent of the second step.
-/
def ParentCommutesWithEquiv
    (S : ProjectedCompressionStep alpha)
    (T : ProjectedCompressionStep beta)
    (e : Equiv alpha beta) : Prop :=
  forall v : alpha, e (S.afterParent v) = T.beforeParent (e v)

end ProjectedCompressionStep

/--
A dependent projected execution.  Each slot may use its own restricted vertex
type; proving that these slots identify with a single restricted forest is the
remaining execution/restriction commutation step.
-/
structure ProjectedCompressionExecution (m : Nat) where
  vertex : Fin m -> Type*
  step : forall i : Fin m, ProjectedCompressionStep (vertex i)

namespace ProjectedCompressionExecution

variable {m : Nat}

/-- Sum of projected step costs. -/
noncomputable def cost (E : ProjectedCompressionExecution m) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i => (E.step i).cost

/-- Source-facing projected execution cost. -/
noncomputable def projectedCost (E : ProjectedCompressionExecution m) : Nat :=
  E.cost

/-- Sum of recurrence-consumable projected step costs. -/
noncomputable def consumableCost (E : ProjectedCompressionExecution m) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i => (E.step i).consumableCost

/-- Sum of exceptional projected step costs. -/
noncomputable def exceptionalCost (E : ProjectedCompressionExecution m) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i => (E.step i).exceptionalCost

/-- Sum of projected nonrootpath indicators. -/
noncomputable def nonrootCount (E : ProjectedCompressionExecution m) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i => (E.step i).nonrootIndicator

/-- Number of charged projected steps. -/
noncomputable def chargedCount (E : ProjectedCompressionExecution m) : Nat :=
  E.nonrootCount

/-- Projected nonroot counts are bounded by the number of projected slots. -/
theorem nonrootCount_le_length (E : ProjectedCompressionExecution m) :
    E.nonrootCount <= m := by
  classical
  unfold nonrootCount
  calc
    Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (E.step i).nonrootIndicator)
        <= Finset.sum (Finset.univ : Finset (Fin m)) (fun _i => (1 : Nat)) := by
          exact Finset.sum_le_sum (by
            intro i _hi
            exact (E.step i).nonrootIndicator_le_one)
    _ = m := by
          simp

/-- Projected charged counts are bounded by the number of projected slots. -/
theorem chargedCount_le_length (E : ProjectedCompressionExecution m) :
    E.chargedCount <= m := by
  simpa [chargedCount] using E.nonrootCount_le_length

/-- Projected execution cost splits into recurrence-consumable and exceptional parts. -/
theorem projectedCost_eq_consumableCost_add_exceptionalCost
    (E : ProjectedCompressionExecution m) :
    E.projectedCost = E.consumableCost + E.exceptionalCost := by
  classical
  unfold projectedCost cost consumableCost exceptionalCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (by
    intro i _hi
    exact (E.step i).cost_eq_consumableCost_add_exceptionalCost)

/-- Consecutive projected slots agree up to a vertex equivalence. -/
def HasConsecutiveStates (E : ProjectedCompressionExecution m) : Prop :=
  forall i j : Fin m, i.val + 1 = j.val ->
    Exists fun e : Equiv (E.vertex i) (E.vertex j) =>
      (E.step i).ParentCommutesWithEquiv (E.step j) e

/--
Semantic validity for dependent projected executions: adjacent parent maps
commute after identifying consecutive restricted vertex types.
-/
def IsSemanticallyValid (E : ProjectedCompressionExecution m) : Prop :=
  E.HasConsecutiveStates

/--
Admissibility for projected executions.  These are first-class projected
objects rather than ordinary source executions; the admissible semantic
condition is the projected consecutive-state condition.
-/
def IsAdmissible (E : ProjectedCompressionExecution m) : Prop :=
  E.IsSemanticallyValid

theorem isSemanticallyValid_iff_hasConsecutiveStates
    (E : ProjectedCompressionExecution m) :
    E.IsSemanticallyValid <-> E.HasConsecutiveStates :=
  Iff.rfl

theorem isAdmissible_iff_isSemanticallyValid
    (E : ProjectedCompressionExecution m) :
    E.IsAdmissible <-> E.IsSemanticallyValid :=
  Iff.rfl

/--
Projected admissibility alone is too weak to imply domination by `topDownCost`:
a one-slot projected execution over `Unit` can have positive projected cost
while the rank-zero base-accounted `topDownCost` is zero.
-/
theorem exists_admissible_projectedCost_gt_topDownCost_rank_zero :
    Exists fun E : ProjectedCompressionExecution.{0} 1 =>
      E.IsAdmissible /\ E.projectedCost = 1 /\ topDownCost 1 1 0 = 0 := by
  classical
  let path : ProjectedPathSegment Unit (fun _ : Unit => ()) := {
    len := 2
    node := fun _ => ()
    parent_chain := by
      intro i j hij
      rfl
  }
  let step : ProjectedCompressionStep Unit := {
    beforeParent := fun _ => ()
    afterParent := fun _ => ()
    path := path
  }
  let E : ProjectedCompressionExecution 1 := {
    vertex := fun _ => Unit
    step := fun _ => step
  }
  refine ⟨E, ?_, ?_, topDownCost_rank_zero_eq_zero 1 1⟩
  · intro i j hij
    omega
  · simp [E, step, path, projectedCost, cost, ProjectedCompressionStep.cost,
      ProjectedPathSegment.edgeCost]

end ProjectedCompressionExecution

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

/--
If the original source path is a rootpath, then a nonempty top projection is a
rootpath in the top restricted forest.
-/
theorem topProjectionSegment_isRootPath_of_source_root
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (hlast : P.LastMatchesTarget)
    (hroot : P.IsRootPath F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (hcut_lt : cut < P.len.val) :
    (P.topProjectionSegment D hchain cut hcut).IsRootPath := by
  intro hlen
  apply Subtype.ext
  let i : Fin (P.topProjectionLength D cut hcut) :=
    (P.topProjectionSegment D hchain cut hcut).lastIndex hlen
  let orig : Fin (n + 1) := P.topProjectionIndex D cut hcut i
  have hi_val : i.val = P.len.val - cut - 1 := by
    simp [i, ProjectedPathSegment.lastIndex, topProjectionSegment, topProjectionLength]
  have horig_last : orig.val + 1 = P.len.val := by
    simp [orig, topProjectionIndex]
    have hcut_le : cut <= P.len.val := hcut.1
    omega
  have horig_target : P.node orig = P.target := hlast orig horig_last
  have hparent : F.parent (P.node orig) = P.node orig := by
    unfold IsRootPath RawRankedForest.IsRoot at hroot
    rw [horig_target, hroot]
  simpa [RawDissection.topParent, topProjectionNode_val, orig] using hparent

/--
If the cut is the full active path and the original path is a rootpath, then
the bottom projection is also a rootpath in the bottom restricted forest.
-/
theorem bottomProjectionSegment_isRootPath_of_source_root_all_bottom
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (hlast : P.LastMatchesTarget)
    (hroot : P.IsRootPath F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (hcut_eq : cut = P.len.val) :
    (P.bottomProjectionSegment D hchain cut hcut).IsRootPath := by
  intro hlen
  apply Subtype.ext
  let i : Fin (P.bottomProjectionLength D cut hcut) :=
    (P.bottomProjectionSegment D hchain cut hcut).lastIndex hlen
  let orig : Fin (n + 1) := P.bottomProjectionIndex D cut hcut i
  have hi_last : i.val = P.bottomProjectionLength D cut hcut - 1 := rfl
  have hbottom_len : P.bottomProjectionLength D cut hcut = cut := rfl
  have horig_last : orig.val + 1 = P.len.val := by
    simp [orig, bottomProjectionIndex]
    omega
  have horig_target : P.node orig = P.target := hlast orig horig_last
  have hparent : F.parent (P.node orig) = P.node orig := by
    unfold IsRootPath RawRankedForest.IsRoot at hroot
    rw [horig_target, hroot]
  have hparent_bottom : D.IsBottom (F.parent (P.node orig)) := by
    have hbottom : D.IsBottom (P.node orig) := (P.bottomProjectionNode D cut hcut i).2
    simpa [hparent] using hbottom
  have hbottom_val :
      (D.bottomParent (P.bottomProjectionNode D cut hcut i)).1 =
        F.parent (P.node orig) :=
    D.bottomParent_val_of_parent_bottom (P.bottomProjectionNode D cut hcut i) hparent_bottom
  exact hbottom_val.trans hparent

/--
If the original source path is nonroot and has a nonempty top suffix, then the
top projection is a nonrootpath in the top restricted forest.
-/
theorem topProjectionSegment_isNonrootPath_of_source_nonroot
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (hlast : P.LastMatchesTarget)
    (hnonroot : P.IsNonrootPath F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (hcut_lt : cut < P.len.val) :
    (P.topProjectionSegment D hchain cut hcut).IsNonrootPath := by
  have hlen : 0 < (P.topProjectionSegment D hchain cut hcut).len := by
    simp [topProjectionSegment, topProjectionLength]
    have hcut_le : cut <= P.len.val := hcut.1
    omega
  apply Exists.intro hlen
  intro heq
  let i : Fin (P.topProjectionLength D cut hcut) :=
    (P.topProjectionSegment D hchain cut hcut).lastIndex hlen
  let orig : Fin (n + 1) := P.topProjectionIndex D cut hcut i
  have hi_val : i.val = P.len.val - cut - 1 := by
    simp [i, ProjectedPathSegment.lastIndex, topProjectionSegment, topProjectionLength]
  have horig_last : orig.val + 1 = P.len.val := by
    simp [orig, topProjectionIndex]
    have hcut_le : cut <= P.len.val := hcut.1
    omega
  have horig_target : P.node orig = P.target := hlast orig horig_last
  have hval : F.parent (P.node orig) = P.node orig := by
    have hval_raw := congrArg Subtype.val heq
    simpa [RawDissection.topParent, topProjectionNode_val, orig] using hval_raw
  unfold IsNonrootPath at hnonroot
  exact hnonroot (by simpa [horig_target] using hval)

/--
Path-level cost accounting in which the one cross-dissection charge is paid by
the top projected nonroot indicator when such a charge is actually needed.
-/
theorem sourceCost_le_projection_edgeCosts_add_topNonrootIndicator
    {n r : Nat}
    {F : RawRankedForest n r}
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (hlast : P.LastMatchesTarget)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.sourceCost F <=
      (P.bottomProjectionSegment D hchain cut hcut).edgeCost +
        (P.topProjectionSegment D hchain cut hcut).edgeCost +
          (P.topProjectionSegment D hchain cut hcut).nonrootIndicator := by
  classical
  by_cases htop : cut < P.len.val
  case pos =>
    by_cases hnonroot : P.IsNonrootPath F
    case pos =>
      have ht_nonroot : (P.topProjectionSegment D hchain cut hcut).IsNonrootPath :=
        P.topProjectionSegment_isNonrootPath_of_source_nonroot
          D hchain hlast hnonroot cut hcut htop
      have ht1 : (P.topProjectionSegment D hchain cut hcut).nonrootIndicator = 1 :=
        (P.topProjectionSegment D hchain cut hcut).nonrootIndicator_eq_one_of_nonroot
          ht_nonroot
      rw [ht1]
      exact P.sourceCost_le_projection_edgeCosts_add_one D hchain cut hcut
    case neg =>
      have hroot : P.IsRootPath F := by
        unfold IsRootPath RawRankedForest.IsRoot
        unfold IsNonrootPath at hnonroot
        exact Decidable.not_not.mp hnonroot
      unfold sourceCost
      rw [if_pos hroot]
      omega
  case neg =>
    have hcut_le : cut <= P.len.val := hcut.1
    have hcut_eq : cut = P.len.val := by omega
    by_cases hroot : P.IsRootPath F
    case pos =>
      unfold sourceCost
      rw [if_pos hroot]
      omega
    case neg =>
      unfold sourceCost
      rw [if_neg hroot]
      unfold cost ProjectedPathSegment.edgeCost
      simp [bottomProjectionSegment, topProjectionSegment, bottomProjectionLength,
        topProjectionLength, hcut_eq]

end RawCompressionPath

namespace RawDissection

variable {n r : Nat} {F G : RawRankedForest n r}

/-- Identity-on-values equivalence between top restricted vertex types. -/
def topEquivOfTopIff
    (D : RawDissection F)
    (D2 : RawDissection G)
    (h : forall v : Fin n, Iff (D.IsTop v) (D2.IsTop v)) :
    Equiv ({v : Fin n // D.IsTop v}) ({v : Fin n // D2.IsTop v}) := {
  toFun := fun v => Subtype.mk v.1 ((h v.1).1 v.2),
  invFun := fun v => Subtype.mk v.1 ((h v.1).2 v.2),
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/-- Identity-on-values equivalence between bottom restricted vertex types. -/
def bottomEquivOfBottomIff
    (D : RawDissection F)
    (D2 : RawDissection G)
    (h : forall v : Fin n, Iff (D.IsBottom v) (D2.IsBottom v)) :
    Equiv ({v : Fin n // D.IsBottom v}) ({v : Fin n // D2.IsBottom v}) := {
  toFun := fun v => Subtype.mk v.1 ((h v.1).1 v.2),
  invFun := fun v => Subtype.mk v.1 ((h v.1).2 v.2),
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/-- Top-side stability gives bottom-side stability by complementation. -/
theorem bottomIffOfTopIff
    (D : RawDissection F)
    (D2 : RawDissection G)
    (h : forall v : Fin n, Iff (D.IsTop v) (D2.IsTop v))
    (v : Fin n) :
    Iff (D.IsBottom v) (D2.IsBottom v) := by
  unfold IsBottom
  exact not_congr (h v)

end RawDissection

namespace RawCompressionStep

variable {n r : Nat}

/-- Over one vertex every raw source step is a rootpath and has zero cost. -/
theorem cost_eq_zero_of_one_vertex (S : RawCompressionStep 1 r) :
    S.cost = 0 := by
  classical
  have hroot : S.path.IsRootPath S.before := by
    unfold RawCompressionPath.IsRootPath RawRankedForest.IsRoot
    exact Subsingleton.elim _ _
  unfold cost RawCompressionPath.sourceCost
  rw [if_pos hroot]

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

/--
The bottom and top projected step nonroot indicators are bounded by the source
nonroot indicator of the original step.  This is the one-step count half of the
projection main lemma.
-/
theorem projected_nonrootIndicators_add_le_nonrootIndicator
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    (S.bottomProjectedStep D hS cut hcut).nonrootIndicator +
        (S.topProjectedStep D hS cut hcut).nonrootIndicator <=
      S.nonrootIndicator := by
  classical
  let B := S.bottomProjectedStep D hS cut hcut
  let T := S.topProjectedStep D hS cut hcut
  change B.nonrootIndicator + T.nonrootIndicator <= S.nonrootIndicator
  by_cases htop : cut < S.path.len.val
  case pos =>
    have hb0 : B.nonrootIndicator = 0 := by
      unfold B RawCompressionPath.ProjectedCompressionStep.nonrootIndicator
      exact S.path.bottomProjectionSegment_nonrootIndicator_eq_zero_of_top_nonempty
        D hS.1.2.2.1 cut hcut htop
    by_cases hnonroot : S.path.IsNonrootPath S.before
    case pos =>
      have ht_le : T.nonrootIndicator <= 1 := T.nonrootIndicator_le_one
      unfold nonrootIndicator
      rw [if_pos hnonroot]
      omega
    case neg =>
      have hroot : S.path.IsRootPath S.before := by
        unfold RawCompressionPath.IsRootPath RawRankedForest.IsRoot
        unfold RawCompressionPath.IsNonrootPath at hnonroot
        exact Decidable.not_not.mp hnonroot
      have ht0 : T.nonrootIndicator = 0 := by
        unfold T RawCompressionPath.ProjectedCompressionStep.nonrootIndicator
        exact (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).nonrootIndicator_eq_zero_of_root
          (S.path.topProjectionSegment_isRootPath_of_source_root D hS.1.2.2.1
            hS.1.2.2.2 hroot cut hcut htop)
      unfold nonrootIndicator
      rw [if_neg hnonroot]
      omega
  case neg =>
    have hcut_le : cut <= S.path.len.val := hcut.1
    have hcut_eq : cut = S.path.len.val := by omega
    have ht0 : T.nonrootIndicator = 0 := by
      unfold T RawCompressionPath.ProjectedCompressionStep.nonrootIndicator
      exact
        (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).nonrootIndicator_eq_zero_of_len_eq_zero
        (by simp [RawCompressionPath.topProjectionSegment,
          RawCompressionPath.topProjectionLength, hcut_eq])
    by_cases hnonroot : S.path.IsNonrootPath S.before
    case pos =>
      have hb_le : B.nonrootIndicator <= 1 := B.nonrootIndicator_le_one
      unfold nonrootIndicator
      rw [if_pos hnonroot]
      omega
    case neg =>
      have hroot : S.path.IsRootPath S.before := by
        unfold RawCompressionPath.IsRootPath RawRankedForest.IsRoot
        unfold RawCompressionPath.IsNonrootPath at hnonroot
        exact Decidable.not_not.mp hnonroot
      have hb0 : B.nonrootIndicator = 0 := by
        unfold B RawCompressionPath.ProjectedCompressionStep.nonrootIndicator
        exact
          (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).nonrootIndicator_eq_zero_of_root
          (S.path.bottomProjectionSegment_isRootPath_of_source_root_all_bottom D hS.1.2.2.1
            hS.1.2.2.2 hroot cut hcut hcut_eq)
      unfold nonrootIndicator
      rw [if_neg hnonroot]
      omega

/--
Step-level cost accounting using the top projected nonroot indicator as the
boundary charge.
-/
theorem cost_le_projectedSteps_cost_add_topNonrootIndicator
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).cost +
          (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
  unfold cost
  exact S.path.sourceCost_le_projection_edgeCosts_add_topNonrootIndicator
    D hS.1.2.2.1 hS.1.2.2.2 cut hcut

/--
For a source nonrootpath, the top projection has no exceptional cost: if the
top suffix is nonempty it is nonroot-like, and if it is empty its edge cost is
zero.
-/
theorem topProjectedStep_cost_eq_consumableCost_of_source_nonroot
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnonroot : S.path.IsNonrootPath S.before) :
    (S.topProjectedStep D hS cut hcut).cost =
      (S.topProjectedStep D hS cut hcut).consumableCost := by
  classical
  let T := S.topProjectedStep D hS cut hcut
  change T.cost = T.consumableCost
  by_cases htop : cut < S.path.len.val
  · have ht_charged : T.IsCharged := by
      unfold T RawCompressionPath.ProjectedCompressionStep.IsCharged
        RawCompressionPath.ProjectedCompressionStep.IsNonrootPath
      exact S.path.topProjectionSegment_isNonrootPath_of_source_nonroot
        D hS.1.2.2.1 hS.1.2.2.2 hnonroot cut hcut htop
    rw [T.consumableCost_eq_cost_of_charged ht_charged]
  · have hcut_eq : cut = S.path.len.val := by
      have hcut_le : cut <= S.path.len.val := hcut.1
      omega
    have hcost : T.cost = 0 := by
      unfold T RawCompressionStep.topProjectedStep
        RawCompressionPath.ProjectedCompressionStep.cost
        RawCompressionPath.ProjectedPathSegment.edgeCost
      simp [RawCompressionPath.topProjectionSegment,
        RawCompressionPath.topProjectionLength, hcut_eq]
    rw [hcost]
    by_cases ht_charged : T.IsCharged
    · rw [T.consumableCost_eq_cost_of_charged ht_charged, hcost]
    · rw [T.consumableCost_eq_zero_of_not_charged ht_charged]

/--
Step-level accounting with the top exceptional projected cost removed.  The
only top-side additive remainder is the already existing projected nonroot
indicator.
-/
theorem cost_le_bottomCost_add_topConsumable_add_topNonroot
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).consumableCost +
          (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
  classical
  by_cases hnonroot : S.path.IsNonrootPath S.before
  · have htop_cost :
        (S.topProjectedStep D hS cut hcut).cost =
          (S.topProjectedStep D hS cut hcut).consumableCost :=
      S.topProjectedStep_cost_eq_consumableCost_of_source_nonroot
        D hS cut hcut hnonroot
    simpa [htop_cost] using
      S.cost_le_projectedSteps_cost_add_topNonrootIndicator D hS cut hcut
  · have hroot : S.path.IsRootPath S.before := by
      unfold RawCompressionPath.IsRootPath RawRankedForest.IsRoot
      unfold RawCompressionPath.IsNonrootPath at hnonroot
      exact Decidable.not_not.mp hnonroot
    unfold cost RawCompressionPath.sourceCost
    rw [if_pos hroot]
    omega

/--
The raw bottom-exceptional cost is not itself bounded by the bottom side size,
even for a valid rank-threshold-origin projected step.  Source rootpaths can
produce root-like bottom projected edge cost that is irrelevant to source cost.
-/
theorem exists_rankThreshold_bottomExceptionalCost_gt_bottomFinset_card :
    Exists fun S : RawCompressionStep 2 1 =>
      Exists fun hS : S.IsValid =>
        let D := RankThresholdDissection.dissection S.before hS.1.1 0
        Exists fun cut : Nat =>
          Exists fun hcut : S.path.HasDissectionCut D cut =>
            D.bottomFinset.card <
              (S.bottomProjectedStep D hS cut hcut).exceptionalCost := by
  classical
  let v0 : Fin 2 := ⟨0, by norm_num⟩
  let F : RawRankedForest 2 1 := {
    parent := fun v => v
    rank := fun v =>
      if v = v0 then ⟨0, by norm_num⟩ else ⟨1, by norm_num⟩
  }
  let P : RawCompressionPath 2 := {
    len := ⟨3, by norm_num⟩
    node := fun _ => v0
    target := v0
  }
  let S : RawCompressionStep 2 1 := {
    before := F
    after := F
    path := P
  }
  have hF : F.IsRankValid := by
    intro v hv
    exact False.elim (hv rfl)
  have hP : P.IsValidFor F := by
    refine ⟨hF, ?_, ?_, ?_⟩
    · norm_num [P]
    · intro i j _hij _hj
      rfl
    · intro i _hi
      rfl
  have hS : S.IsValid := by
    refine ⟨hP, hF, ?_, ?_, ?_, ?_⟩
    · intro v
      rfl
    · intro _hroot
      rfl
    · intro hnonroot _v _hcomp
      exact False.elim (hnonroot rfl)
    · intro _v _hnot
      rfl
  let D := RankThresholdDissection.dissection S.before hS.1.1 0
  have hcut : S.path.HasDissectionCut D 3 := by
    refine ⟨?_, ?_, ?_⟩
    · norm_num [S, P]
    · intro i _hia _hilt
      simp [D, S, P, F, v0, RankThresholdDissection.dissection,
        RankThresholdDissection.topPred, RawDissection.IsBottom,
        RawDissection.IsTop, RawRankedForest.rankNat]
    · intro i hia hcut_le
      have : False := by
        have hi_lt : i.val < 3 := i.isLt
        omega
      exact False.elim this
  refine ⟨S, hS, 3, hcut, ?_⟩
  have hroot : S.path.IsRootPath S.before := by
    rfl
  have hbottom_root :
      (S.bottomProjectedStep D hS 3 hcut).IsRootLike := by
    unfold RawCompressionPath.ProjectedCompressionStep.IsRootLike
    exact S.path.bottomProjectionSegment_isRootPath_of_source_root_all_bottom
      D hS.1.2.2.1 hS.1.2.2.2 hroot 3 hcut rfl
  have hnot_charged : Not (S.bottomProjectedStep D hS 3 hcut).IsCharged :=
    ((S.bottomProjectedStep D hS 3 hcut).not_charged_iff_rootLike).2 hbottom_root
  rw [(S.bottomProjectedStep D hS 3 hcut).exceptionalCost_eq_cost_of_not_charged
    hnot_charged]
  have hcard : D.bottomFinset.card = 1 := by
    have hset : D.bottomFinset = {v0} := by
      ext v
      fin_cases v <;>
        simp [D, S, F, v0, RankThresholdDissection.dissection,
          RankThresholdDissection.topPred, RawDissection.bottomFinset,
          RawDissection.IsBottom, RawDissection.IsTop, RawRankedForest.rankNat]
    rw [hset]
    simp
  have hcost : (S.bottomProjectedStep D hS 3 hcut).cost = 2 := by
    change (S.path.bottomProjectionSegment D hS.1.2.2.1 3 hcut).edgeCost = 2
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost
    rw [RawCompressionPath.bottomProjectionSegment_len]
    rfl
  rw [hcard, hcost]
  norm_num

/--
Top restricted vertices are preserved by `afterDissection`, packaged as the
identity-on-values equivalence needed for execution commutation.
-/
def afterDissectionTopEquiv
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    Equiv D.TopNode ({v : Fin n // (S.afterDissection D hS).IsTop v}) := {
  toFun := fun v => Subtype.mk v.1 (by simpa using v.2),
  invFun := fun v => Subtype.mk v.1 (by simpa using v.2),
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/--
Bottom restricted vertices are preserved by `afterDissection`, packaged as the
identity-on-values equivalence needed for execution commutation.
-/
def afterDissectionBottomEquiv
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    Equiv D.BottomNode ({v : Fin n // (S.afterDissection D hS).IsBottom v}) := {
  toFun := fun v => Subtype.mk v.1 (by simpa using v.2),
  invFun := fun v => Subtype.mk v.1 (by simpa using v.2),
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/--
The projected top after-parent agrees, under `afterDissectionTopEquiv`, with
the top restricted parent map of the after-dissection.
-/
theorem afterDissectionTopEquiv_afterTopParent
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.TopNode) :
    S.afterDissectionTopEquiv D hS (S.afterTopParent D hS v) =
      (S.afterDissection D hS).topParent (S.afterDissectionTopEquiv D hS v) := by
  apply Subtype.ext
  change (S.afterTopParent D hS v).1 =
    ((S.afterDissection D hS).topParent (S.afterDissectionTopEquiv D hS v)).1
  rfl

/--
The projected bottom after-parent agrees, under `afterDissectionBottomEquiv`,
with the bottom restricted parent map of the after-dissection.
-/
theorem afterDissectionBottomEquiv_afterBottomParent
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.BottomNode) :
    S.afterDissectionBottomEquiv D hS (S.afterBottomParent D hS v) =
      (S.afterDissection D hS).bottomParent
        (S.afterDissectionBottomEquiv D hS v) := by
  apply Subtype.ext
  change (S.afterBottomParent D hS v).1 =
    ((S.afterDissection D hS).bottomParent
      (S.afterDissectionBottomEquiv D hS v)).1
  classical
  by_cases hparent : D.IsBottom (S.after.parent v.1)
  case pos =>
    have hafter : (S.afterDissection D hS).IsBottom (S.after.parent v.1) := by
      simpa using hparent
    have hleft : (S.afterBottomParent D hS v).1 = S.after.parent v.1 :=
      S.afterBottomParent_val_of_parent_bottom D hS v hparent
    have hright :
        ((S.afterDissection D hS).bottomParent
          (S.afterDissectionBottomEquiv D hS v)).1 =
          S.after.parent v.1 := by
      exact (S.afterDissection D hS).bottomParent_val_of_parent_bottom
        (S.afterDissectionBottomEquiv D hS v) hafter
    rw [hleft, hright]
  case neg =>
    have htop : D.IsTop (S.after.parent v.1) := by
      unfold RawDissection.IsBottom at hparent
      exact Decidable.not_not.mp hparent
    have hafterTop : (S.afterDissection D hS).IsTop (S.after.parent v.1) := by
      simpa using htop
    have hleft : (S.afterBottomParent D hS v).1 = v.1 :=
      S.afterBottomParent_val_of_parent_top D hS v htop
    have hright :
        ((S.afterDissection D hS).bottomParent
          (S.afterDissectionBottomEquiv D hS v)).1 =
          v.1 := by
      exact (S.afterDissection D hS).bottomParent_val_of_parent_top
        (S.afterDissectionBottomEquiv D hS v) hafterTop
    rw [hleft, hright]

/--
Adjacent top projected steps commute under a side-preserving vertex
equivalence when the raw after-state of the first step is the before-state of
the second.
-/
theorem topProjectedStep_after_commutes_with_next_before
    (S T : RawCompressionStep n r)
    (D : RawDissection S.before)
    (D2 : RawDissection T.before)
    (hS : S.IsValid)
    (_hT : T.IsValid)
    (hstate : S.after = T.before)
    (htop : forall v : Fin n, Iff (D.IsTop v) (D2.IsTop v))
    (cutS cutT : Nat)
    (hcutS : S.path.HasDissectionCut D cutS)
    (hcutT : T.path.HasDissectionCut D2 cutT) :
    (S.topProjectedStep D hS cutS hcutS).ParentCommutesWithEquiv
      (T.topProjectedStep D2 _hT cutT hcutT)
      (D.topEquivOfTopIff D2 htop) := by
  intro v
  apply Subtype.ext
  change (S.afterTopParent D hS v).1 =
    (D2.topParent ((D.topEquivOfTopIff D2 htop) v)).1
  simp [RawDissection.topParent, afterTopParent, RawDissection.topEquivOfTopIff, hstate]

/--
Adjacent bottom projected steps commute under a side-preserving vertex
equivalence when the raw after-state of the first step is the before-state of
the second.
-/
theorem bottomProjectedStep_after_commutes_with_next_before
    (S T : RawCompressionStep n r)
    (D : RawDissection S.before)
    (D2 : RawDissection T.before)
    (hS : S.IsValid)
    (_hT : T.IsValid)
    (hstate : S.after = T.before)
    (hbottom : forall v : Fin n, Iff (D.IsBottom v) (D2.IsBottom v))
    (cutS cutT : Nat)
    (hcutS : S.path.HasDissectionCut D cutS)
    (hcutT : T.path.HasDissectionCut D2 cutT) :
    (S.bottomProjectedStep D hS cutS hcutS).ParentCommutesWithEquiv
      (T.bottomProjectedStep D2 _hT cutT hcutT)
      (D.bottomEquivOfBottomIff D2 hbottom) := by
  intro v
  apply Subtype.ext
  change (S.afterBottomParent D hS v).1 =
    (D2.bottomParent ((D.bottomEquivOfBottomIff D2 hbottom) v)).1
  classical
  by_cases hb : D.IsBottom (S.after.parent v.1)
  case pos =>
    have hb2 : D2.IsBottom (T.before.parent v.1) := by
      have hb2raw : D2.IsBottom (S.after.parent v.1) :=
        (hbottom (S.after.parent v.1)).1 hb
      simpa [hstate] using hb2raw
    have hleft : (S.afterBottomParent D hS v).1 = S.after.parent v.1 :=
      S.afterBottomParent_val_of_parent_bottom D hS v hb
    have hright :
        (D2.bottomParent ((D.bottomEquivOfBottomIff D2 hbottom) v)).1 =
          T.before.parent v.1 := by
      exact D2.bottomParent_val_of_parent_bottom
        ((D.bottomEquivOfBottomIff D2 hbottom) v) hb2
    rw [hleft, hright, hstate]
  case neg =>
    have ht : D.IsTop (S.after.parent v.1) := by
      unfold RawDissection.IsBottom at hb
      exact Decidable.not_not.mp hb
    have hb2not : Not (D2.IsBottom (T.before.parent v.1)) := by
      intro hb2
      have hb2' : D2.IsBottom (S.after.parent v.1) := by
        simpa [hstate] using hb2
      exact hb ((hbottom (S.after.parent v.1)).2 hb2')
    have ht2 : D2.IsTop (T.before.parent v.1) := by
      unfold RawDissection.IsBottom at hb2not
      exact Decidable.not_not.mp hb2not
    have hleft : (S.afterBottomParent D hS v).1 = v.1 :=
      S.afterBottomParent_val_of_parent_top D hS v ht
    have hright :
        (D2.bottomParent ((D.bottomEquivOfBottomIff D2 hbottom) v)).1 =
          v.1 := by
      exact D2.bottomParent_val_of_parent_top
        ((D.bottomEquivOfBottomIff D2 hbottom) v) ht2
    rw [hleft, hright]

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

/-- Over one vertex every raw execution has zero cost. -/
theorem cost_eq_zero_of_one_vertex
    (E : RawCompressionExecution m 1 r) :
    E.cost = 0 := by
  rw [E.cost_eq_stepCostSum]
  unfold stepCostSum
  exact Finset.sum_eq_zero (by
    intro i _hi
    exact RawCompressionStep.cost_eq_zero_of_one_vertex (E.step i))

/-- The ordinary base-accounted top-down cost over one vertex is zero. -/
theorem topDownCost_one_vertex_eq_zero (m r : Nat) :
    topDownCost m 1 r = 0 := by
  exact Nat.eq_zero_of_le_zero (by
    apply topDownCost_le_of_forall_valid
    intro E _hE
    rw [E.cost_eq_zero_of_one_vertex])

end RawCompressionExecution

namespace RawCompressionPath.ProjectedCompressionExecution

/--
The projected counterexample persists at every rank bound over one ordinary
vertex, since ordinary one-vertex executions have zero cost.
-/
theorem exists_admissible_projectedCost_gt_topDownCost_one_vertex
    (r : Nat) :
    Exists fun E : ProjectedCompressionExecution.{0} 1 =>
      E.IsAdmissible /\ E.projectedCost = 1 /\ topDownCost 1 1 r = 0 := by
  rcases exists_admissible_projectedCost_gt_topDownCost_rank_zero with
    ⟨E, hAdm, hCost, _hZero⟩
  exact ⟨E, hAdm, hCost, RawCompressionExecution.topDownCost_one_vertex_eq_zero 1 r⟩

end RawCompressionPath.ProjectedCompressionExecution

namespace RawCompressionExecution

variable {m n r : Nat}

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

/--
Bottom-side vertex budget for projected source accounting.  For stable
dissection families this is the paper's `|X_b|`; for arbitrary step-indexed
families it is the finite supremum over the displayed bottom sides.
-/
noncomputable def bottomBoundaryCard
    (E : RawCompressionExecution m n r)
    (D : forall i : Fin m, RawDissection (E.step i).before) : Nat :=
  (Finset.univ : Finset (Fin m)).sup fun i => (D i).bottomFinset.card

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

/-- Sum of bottom projected nonrootpath indicators for a chosen family of cuts. -/
noncomputable def bottomProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator

/-- Sum of top projected nonrootpath indicators for a chosen family of cuts. -/
noncomputable def topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator

/-- Dependent bottom projected execution for a chosen family of cuts. -/
noncomputable def bottomProjectedExecution
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    RawCompressionPath.ProjectedCompressionExecution m where
  vertex := fun i => (D i).BottomNode
  step := fun i => (E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)

/-- Dependent top projected execution for a chosen family of cuts. -/
noncomputable def topProjectedExecution
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    RawCompressionPath.ProjectedCompressionExecution m where
  vertex := fun i => (D i).TopNode
  step := fun i => (E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)

/-- Canonical-cut bottom projected execution. -/
noncomputable def canonicalBottomProjectedExecution
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    RawCompressionPath.ProjectedCompressionExecution m :=
  E.bottomProjectedExecution hsteps D (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/-- Canonical-cut top projected execution. -/
noncomputable def canonicalTopProjectedExecution
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    RawCompressionPath.ProjectedCompressionExecution m :=
  E.topProjectedExecution hsteps D (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

@[simp]
theorem bottomProjectedExecution_cost
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).cost =
      E.bottomProjectedCostSum hsteps D cut hcut :=
  rfl

@[simp]
theorem topProjectedExecution_cost
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).cost =
      E.topProjectedCostSum hsteps D cut hcut :=
  rfl

@[simp]
theorem bottomProjectedExecution_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).nonrootCount =
      E.bottomProjectedNonrootCount hsteps D cut hcut :=
  rfl

@[simp]
theorem topProjectedExecution_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).nonrootCount =
      E.topProjectedNonrootCount hsteps D cut hcut :=
  rfl

/-- Bottom-side stability for adjacent dissections, derived from top stability. -/
theorem bottomSideStable_of_topSideStable
    (E : RawCompressionExecution m n r)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v))
    (i j : Fin m)
    (hij : i.val + 1 = j.val)
    (v : Fin n) :
    Iff ((D i).IsBottom v) ((D j).IsBottom v) :=
  (D i).bottomIffOfTopIff (D j) (htop i j hij) v

/--
The bottom dependent projected execution has consecutive states up to
side-preserving equivalences.
-/
theorem bottomProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).HasConsecutiveStates := by
  intro i j hij
  refine Exists.intro ((D i).bottomEquivOfBottomIff (D j) (hbottom i j hij)) ?_
  exact (E.step i).bottomProjectedStep_after_commutes_with_next_before
    (E.step j) (D i) (D j) (hsteps i) (hsteps j) (hstate i j hij)
    (hbottom i j hij) (cut i) (cut j) (hcut i) (hcut j)

/--
The top dependent projected execution has consecutive states up to
side-preserving equivalences.
-/
theorem topProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).HasConsecutiveStates := by
  intro i j hij
  refine Exists.intro ((D i).topEquivOfTopIff (D j) (htop i j hij)) ?_
  exact (E.step i).topProjectedStep_after_commutes_with_next_before
    (E.step j) (D i) (D j) (hsteps i) (hsteps j) (hstate i j hij)
    (htop i j hij) (cut i) (cut j) (hcut i) (hcut j)

/--
The bottom dependent projected execution is semantically valid in the projected
execution API.
-/
theorem bottomProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).IsSemanticallyValid :=
  E.bottomProjectedExecution_hasConsecutiveStates hsteps hstate D hbottom cut hcut

/--
The top dependent projected execution is semantically valid in the projected
execution API.
-/
theorem topProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).IsSemanticallyValid :=
  E.topProjectedExecution_hasConsecutiveStates hsteps hstate D htop cut hcut

/-- The bottom dependent projected execution is admissible in the projected API. -/
theorem bottomProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).IsAdmissible :=
  E.bottomProjectedExecution_isSemanticallyValid hsteps hstate D hbottom cut hcut

/-- The top dependent projected execution is admissible in the projected API. -/
theorem topProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v))
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).IsAdmissible :=
  E.topProjectedExecution_isSemanticallyValid hsteps hstate D htop cut hcut

/-- Canonical-cut bottom projected execution consecutive-state theorem. -/
theorem canonicalBottomProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v)) :
    (E.canonicalBottomProjectedExecution hE.1 D).HasConsecutiveStates := by
  exact E.bottomProjectedExecution_hasConsecutiveStates hE.1 hE.2.1 D hbottom
    (E.dissectionCut hE.1 D) (E.dissectionCut_spec hE.1 D)

/-- Canonical-cut top projected execution consecutive-state theorem. -/
theorem canonicalTopProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v)) :
    (E.canonicalTopProjectedExecution hE.1 D).HasConsecutiveStates := by
  exact E.topProjectedExecution_hasConsecutiveStates hE.1 hE.2.1 D htop
    (E.dissectionCut hE.1 D) (E.dissectionCut_spec hE.1 D)

/-- Canonical-cut bottom projected execution semantic-validity theorem. -/
theorem canonicalBottomProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v)) :
    (E.canonicalBottomProjectedExecution hE.1 D).IsSemanticallyValid := by
  exact E.canonicalBottomProjectedExecution_hasConsecutiveStates hE D hbottom

/-- Canonical-cut top projected execution semantic-validity theorem. -/
theorem canonicalTopProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v)) :
    (E.canonicalTopProjectedExecution hE.1 D).IsSemanticallyValid := by
  exact E.canonicalTopProjectedExecution_hasConsecutiveStates hE D htop

/-- Canonical-cut bottom projected execution admissibility theorem. -/
theorem canonicalBottomProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (hbottom : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsBottom v) ((D j).IsBottom v)) :
    (E.canonicalBottomProjectedExecution hE.1 D).IsAdmissible := by
  exact E.canonicalBottomProjectedExecution_isSemanticallyValid hE D hbottom

/-- Canonical-cut top projected execution admissibility theorem. -/
theorem canonicalTopProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (htop : forall i j : Fin m, i.val + 1 = j.val ->
      forall v : Fin n, Iff ((D i).IsTop v) ((D j).IsTop v)) :
    (E.canonicalTopProjectedExecution hE.1 D).IsAdmissible := by
  exact E.canonicalTopProjectedExecution_isSemanticallyValid hE D htop

/-- Rank-threshold dissection attached to each raw execution slot. -/
def rankThresholdDissectionFamily
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (s : Nat)
    (i : Fin m) : RawDissection (E.step i).before :=
  RankThresholdDissection.dissection (E.step i).before (hsteps i).1.1 s

/--
Ranks are stable across adjacent raw execution slots, because a valid step
preserves ranks and the raw execution connects after-state to next before-state.
-/
theorem rankThresholdDissectionFamily_rankNat_eq_of_adjacent
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (i j : Fin m)
    (hij : i.val + 1 = j.val)
    (v : Fin n) :
    RawRankedForest.rankNat (E.step i).before v =
      RawRankedForest.rankNat (E.step j).before v := by
  unfold RawRankedForest.rankNat
  have hrank : (E.step i).after.rank v = (E.step i).before.rank v :=
    (hsteps i).2.2.1 v
  rw [hrank.symm]
  rw [hstate i j hij]

/-- Rank-threshold top sides are stable across adjacent execution slots. -/
theorem rankThresholdDissectionFamily_topStable
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i j : Fin m)
    (hij : i.val + 1 = j.val)
    (v : Fin n) :
    Iff ((E.rankThresholdDissectionFamily hsteps s i).IsTop v)
      ((E.rankThresholdDissectionFamily hsteps s j).IsTop v) := by
  unfold rankThresholdDissectionFamily
  simp only [RankThresholdDissection.dissection_isTop]
  rw [E.rankThresholdDissectionFamily_rankNat_eq_of_adjacent hsteps hstate i j hij v]

/--
The canonical top projected execution for a rank-threshold dissection has
consecutive states up to the projected equivalences.
-/
theorem rankThresholdTopProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).HasConsecutiveStates := by
  exact E.canonicalTopProjectedExecution_hasConsecutiveStates hE
    (E.rankThresholdDissectionFamily hE.1 s)
    (E.rankThresholdDissectionFamily_topStable hE.1 hE.2.1 s)

/--
The canonical bottom projected execution for a rank-threshold dissection has
consecutive states up to the projected equivalences.
-/
theorem rankThresholdBottomProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).HasConsecutiveStates := by
  exact E.canonicalBottomProjectedExecution_hasConsecutiveStates hE
    (E.rankThresholdDissectionFamily hE.1 s)
    (fun i j hij v => E.bottomSideStable_of_topSideStable
      (E.rankThresholdDissectionFamily hE.1 s)
      (E.rankThresholdDissectionFamily_topStable hE.1 hE.2.1 s) i j hij v)

/--
The canonical top projected execution for a rank-threshold dissection is
semantically valid in the projected execution API.
-/
theorem rankThresholdTopProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).IsSemanticallyValid := by
  exact E.rankThresholdTopProjectedExecution_hasConsecutiveStates hE s

/--
The canonical bottom projected execution for a rank-threshold dissection is
semantically valid in the projected execution API.
-/
theorem rankThresholdBottomProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).IsSemanticallyValid := by
  exact E.rankThresholdBottomProjectedExecution_hasConsecutiveStates hE s

/--
The canonical top projected execution for a rank-threshold dissection is
admissible in the projected execution API.
-/
theorem rankThresholdTopProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).IsAdmissible := by
  exact E.rankThresholdTopProjectedExecution_isSemanticallyValid hE s

/--
The canonical bottom projected execution for a rank-threshold dissection is
admissible in the projected execution API.
-/
theorem rankThresholdBottomProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).IsAdmissible := by
  exact E.rankThresholdBottomProjectedExecution_isSemanticallyValid hE s

/-- Bound a displayed bottom-boundary budget by any common bottom-card bound. -/
theorem bottomBoundaryCard_le_of_forall_bottom_card_le
    (E : RawCompressionExecution m n r)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    {b : Nat}
    (hcard : forall i : Fin m, (D i).bottomFinset.card <= b) :
    E.bottomBoundaryCard D <= b := by
  classical
  unfold bottomBoundaryCard
  refine Finset.sup_le ?_
  intro i _hi
  exact hcard i

/-- Identify the bottom-boundary budget when all displayed bottom sides agree. -/
theorem bottomBoundaryCard_eq_of_forall_bottomFinset_eq
    (E : RawCompressionExecution m n r)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (i0 : Fin m)
    (hstable : forall i : Fin m, (D i).bottomFinset = (D i0).bottomFinset) :
    E.bottomBoundaryCard D = (D i0).bottomFinset.card := by
  classical
  apply le_antisymm
  · exact E.bottomBoundaryCard_le_of_forall_bottom_card_le D (by
      intro i
      rw [hstable i])
  · unfold bottomBoundaryCard
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => (D i).bottomFinset.card)
      (Finset.mem_univ i0)

/--
In a semantically valid execution, rank-threshold dissections compute the same
rank for a vertex at every slot, measured against any chosen slot.
-/
theorem rankThresholdDissectionFamily_rankNat_eq_of_slot
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (i0 i : Fin m)
    (v : Fin n) :
    RawRankedForest.rankNat (E.step i).before v =
      RawRankedForest.rankNat (E.step i0).before v := by
  have hm_pos : 0 < m := lt_of_le_of_lt (Nat.zero_le i0.val) i0.isLt
  let first : Fin m := ⟨0, hm_pos⟩
  have hto_first :
      forall t : Nat, forall ht : t < m,
        RawRankedForest.rankNat (E.step ⟨t, ht⟩).before v =
          RawRankedForest.rankNat (E.step first).before v := by
    intro t
    induction t with
    | zero =>
        intro ht
        rfl
    | succ t ih =>
        intro ht
        let prev : Fin m := ⟨t, by omega⟩
        let curr : Fin m := ⟨t + 1, ht⟩
        have hadj : prev.val + 1 = curr.val := rfl
        have hprev_curr :
            RawRankedForest.rankNat (E.step prev).before v =
              RawRankedForest.rankNat (E.step curr).before v :=
          E.rankThresholdDissectionFamily_rankNat_eq_of_adjacent
            hsteps hstate prev curr hadj v
        calc
          RawRankedForest.rankNat (E.step ⟨Nat.succ t, ht⟩).before v
              = RawRankedForest.rankNat (E.step curr).before v := rfl
          _ = RawRankedForest.rankNat (E.step prev).before v := hprev_curr.symm
          _ = RawRankedForest.rankNat (E.step first).before v := ih (by omega)
  calc
    RawRankedForest.rankNat (E.step i).before v
        = RawRankedForest.rankNat (E.step first).before v :=
          hto_first i.val i.isLt
    _ = RawRankedForest.rankNat (E.step i0).before v :=
          (hto_first i0.val i0.isLt).symm

/-- Rank-threshold bottom vertex sets are stable across all execution slots. -/
theorem rankThresholdDissectionFamily_bottomFinset_eq_of_slot
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i0 i : Fin m) :
    (E.rankThresholdDissectionFamily hsteps s i).bottomFinset =
      (E.rankThresholdDissectionFamily hsteps s i0).bottomFinset := by
  classical
  ext v
  simp [rankThresholdDissectionFamily,
    E.rankThresholdDissectionFamily_rankNat_eq_of_slot hsteps hstate i0 i v]

/-- Rank-threshold top vertex sets are stable across all execution slots. -/
theorem rankThresholdDissectionFamily_topFinset_eq_of_slot
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i0 i : Fin m) :
    (E.rankThresholdDissectionFamily hsteps s i).topFinset =
      (E.rankThresholdDissectionFamily hsteps s i0).topFinset := by
  classical
  ext v
  simp [rankThresholdDissectionFamily,
    E.rankThresholdDissectionFamily_rankNat_eq_of_slot hsteps hstate i0 i v]

/--
For a nonempty valid execution, the finite `bottomBoundaryCard` of the
rank-threshold family is bounded by the bottom side at any chosen slot.  This
is the formal bridge between the supremum-shaped boundary budget and the
stable paper-side `|X_b|`.
-/
theorem rankThreshold_bottomBoundaryCard_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.bottomBoundaryCard (E.rankThresholdDissectionFamily hE.1 s) <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) := by
  refine E.bottomBoundaryCard_le_of_forall_bottom_card_le
    (E.rankThresholdDissectionFamily hE.1 s) ?_
  intro i
  have hfinset :
      (E.rankThresholdDissectionFamily hE.1 s i).bottomFinset =
        (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset :=
    E.rankThresholdDissectionFamily_bottomFinset_eq_of_slot hE.1 hE.2.1 s i0 i
  rw [hfinset]

/--
For a nonempty valid execution, the finite `bottomBoundaryCard` of the
rank-threshold family is exactly the bottom side at any chosen slot.
-/
theorem rankThreshold_bottomBoundaryCard_eq_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.bottomBoundaryCard (E.rankThresholdDissectionFamily hE.1 s) =
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) := by
  exact E.bottomBoundaryCard_eq_of_forall_bottomFinset_eq
    (E.rankThresholdDissectionFamily hE.1 s) i0
    (fun i => E.rankThresholdDissectionFamily_bottomFinset_eq_of_slot
      hE.1 hE.2.1 s i0 i)

/-- Slot-level bottom rank bound for the rank-threshold dissection family. -/
theorem rankThresholdDissectionFamily_bottom_rank_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (s : Nat)
    (i : Fin m)
    (v : (E.rankThresholdDissectionFamily hsteps s i).BottomNode) :
    RawRankedForest.rankNat (E.step i).before v.1 <= s := by
  exact RankThresholdDissection.bottom_rank_le (E.step i).before (hsteps i).1.1 s v

/-- Slot-level shifted top rank bound for the rank-threshold dissection family. -/
theorem rankThresholdDissectionFamily_top_shifted_rank_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (s : Nat)
    (i : Fin m)
    (v : (E.rankThresholdDissectionFamily hsteps s i).TopNode) :
    RankThresholdDissection.topShiftedRank (E.step i).before (hsteps i).1.1 s v <=
      r - s - 1 := by
  exact RankThresholdDissection.top_shifted_rank_le
    (E.step i).before (hsteps i).1.1 s v

/--
Slot-level top cardinality bound for rank-threshold dissections, conditional
on the existing packing witness carried by the concrete model.
-/
theorem rankThresholdDissectionFamily_top_card_le_div
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (s : Nat)
    (i : Fin m)
    (P : RankThresholdDissection.TopPacking (E.step i).before (hsteps i).1.1 s) :
    (E.rankThresholdDissectionFamily hsteps s i).topFinset.card <=
      n / 2 ^ (s + 1) := by
  exact RankThresholdDissection.top_card_le_div (E.step i).before (hsteps i).1.1 s P

/--
Top-side cardinality bound transported across the stable rank-threshold family
from a packing witness at a chosen slot.
-/
theorem rankThresholdDissectionFamily_top_card_le_div_of_slot_packing
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i0 i : Fin m)
    (P : RankThresholdDissection.TopPacking (E.step i0).before (hsteps i0).1.1 s) :
    (E.rankThresholdDissectionFamily hsteps s i).topFinset.card <=
      n / 2 ^ (s + 1) := by
  have hfinset :
      (E.rankThresholdDissectionFamily hsteps s i).topFinset =
        (E.rankThresholdDissectionFamily hsteps s i0).topFinset :=
    E.rankThresholdDissectionFamily_topFinset_eq_of_slot hsteps hstate s i0 i
  rw [hfinset]
  exact E.rankThresholdDissectionFamily_top_card_le_div hsteps s i0 P

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
Execution-level projected nonroot-count inequality for a chosen family of
dissection cuts.  This is the raw finite analogue of
`|C_b| + |C_t| <= |C|`, before projected steps are reassembled as restricted
source executions.
-/
theorem projectedNonrootCounts_add_le_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.bottomProjectedNonrootCount hsteps D cut hcut +
        E.topProjectedNonrootCount hsteps D cut hcut <=
      E.nonrootCount := by
  classical
  unfold bottomProjectedNonrootCount topProjectedNonrootCount
  let B : Fin m -> Nat := fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator
  let T : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator
  let N : Fin m -> Nat := fun i => (E.step i).nonrootIndicator
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i) <=
        Finset.sum (Finset.univ : Finset (Fin m)) N := by
    exact Finset.sum_le_sum (by
      intro i _hi
      change B i + T i <= N i
      exact (E.step i).projected_nonrootIndicators_add_le_nonrootIndicator
        (D i) (hsteps i) (cut i) (hcut i))
  have hsplit :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i) =
        Finset.sum (Finset.univ : Finset (Fin m)) B +
          Finset.sum (Finset.univ : Finset (Fin m)) T := by
    rw [Finset.sum_add_distrib]
  have hN : Finset.sum (Finset.univ : Finset (Fin m)) N = E.nonrootCount := by
    exact E.nonrootIndicator_sum_eq_nonrootCount
  rw [hsplit.symm]
  exact le_trans hsum (le_of_eq hN)

/-- Canonical-cut form of the execution-level projected nonroot-count bound. -/
theorem canonicalProjectedNonrootCounts_add_le_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.bottomProjectedNonrootCount hsteps D (E.dissectionCut hsteps D)
        (E.dissectionCut_spec hsteps D) +
        E.topProjectedNonrootCount hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) <=
      E.nonrootCount := by
  exact E.projectedNonrootCounts_add_le_nonrootCount hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Execution-level projected cost accounting with the top projected nonroot count
as the boundary term.
-/
theorem stepCostSum_le_projectedCostSums_add_topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D cut hcut +
        E.topProjectedCostSum hsteps D cut hcut +
          E.topProjectedNonrootCount hsteps D cut hcut := by
  classical
  unfold stepCostSum bottomProjectedCostSum topProjectedCostSum topProjectedNonrootCount
  let B : Fin m -> Nat := fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost
  let T : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost
  let N : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (E.step i).cost) <=
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      change (E.step i).cost <= B i + T i + N i
      exact (E.step i).cost_le_projectedSteps_cost_add_topNonrootIndicator
        (D i) (hsteps i) (cut i) (hcut i))
  have hsplit :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i) =
        Finset.sum (Finset.univ : Finset (Fin m)) B +
          Finset.sum (Finset.univ : Finset (Fin m)) T +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
    calc
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i)
          = Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i) +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.sum (Finset.univ : Finset (Fin m)) B +
              Finset.sum (Finset.univ : Finset (Fin m)) T) +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.univ : Finset (Fin m)) B +
            Finset.sum (Finset.univ : Finset (Fin m)) T +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rfl
  exact le_trans hsum (le_of_eq hsplit)

/--
Execution-level accounting with top exceptional projected costs removed.  This
is still not a `topDownCost` consumption theorem: the bottom projected cost
remains a full projected cost.
-/
theorem stepCostSum_le_bottomProjectedCostSum_add_topConsumableCost_add_topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D cut hcut +
        (E.topProjectedExecution hsteps D cut hcut).consumableCost +
          E.topProjectedNonrootCount hsteps D cut hcut := by
  classical
  unfold stepCostSum bottomProjectedCostSum topProjectedNonrootCount
  unfold RawCompressionPath.ProjectedCompressionExecution.consumableCost
  let B : Fin m -> Nat := fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).cost
  let T : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).consumableCost
  let N : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (E.step i).cost) <=
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      change (E.step i).cost <= B i + T i + N i
      exact (E.step i).cost_le_bottomCost_add_topConsumable_add_topNonroot
        (D i) (hsteps i) (cut i) (hcut i))
  have hsplit :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i) =
        Finset.sum (Finset.univ : Finset (Fin m)) B +
          Finset.sum (Finset.univ : Finset (Fin m)) T +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
    calc
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i + N i)
          = Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + T i) +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.sum (Finset.univ : Finset (Fin m)) B +
              Finset.sum (Finset.univ : Finset (Fin m)) T) +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.univ : Finset (Fin m)) B +
            Finset.sum (Finset.univ : Finset (Fin m)) T +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              rfl
  exact le_trans hsum (le_of_eq hsplit)

/-- Canonical-cut form of the sharper execution-level projected cost bound. -/
theorem stepCostSum_le_canonicalProjectedCostSums_add_topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.stepCostSum <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
          E.topProjectedNonrootCount hsteps D (E.dissectionCut hsteps D)
            (E.dissectionCut_spec hsteps D) := by
  exact E.stepCostSum_le_projectedCostSums_add_topProjectedNonrootCount hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Sharper execution-level projected cost accounting stated for the charge-unit
execution cost used by `topDownCost`.
-/
theorem cost_le_canonicalProjectedCostSums_add_topProjectedNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      E.bottomProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
        E.topProjectedCostSum hsteps D (E.dissectionCut hsteps D)
          (E.dissectionCut_spec hsteps D) +
          E.topProjectedNonrootCount hsteps D (E.dissectionCut hsteps D)
            (E.dissectionCut_spec hsteps D) := by
  rw [E.cost_eq_stepCostSum]
  exact E.stepCostSum_le_canonicalProjectedCostSums_add_topProjectedNonrootCount hsteps D

/--
Main-lemma-shaped nonroot-count inequality for the dependent projected
executions.
-/
theorem projectedExecutions_nonrootCount_add_le_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).nonrootCount +
        (E.topProjectedExecution hsteps D cut hcut).nonrootCount <=
      E.nonrootCount := by
  exact E.projectedNonrootCounts_add_le_nonrootCount hsteps D cut hcut

/-- Canonical-cut form of the projected-execution nonroot-count inequality. -/
theorem canonicalProjectedExecutions_nonrootCount_add_le_nonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    (E.canonicalBottomProjectedExecution hsteps D).nonrootCount +
        (E.canonicalTopProjectedExecution hsteps D).nonrootCount <=
      E.nonrootCount := by
  exact E.projectedNonrootCounts_add_le_nonrootCount hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Main-lemma-shaped cost inequality for the dependent projected executions.  This
is the closest current theorem to the paper statement before proving that the
dependent projected executions are genuine restricted source executions.
-/
theorem cost_le_projectedExecutions_cost_add_topNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.cost <=
      (E.bottomProjectedExecution hsteps D cut hcut).cost +
        (E.topProjectedExecution hsteps D cut hcut).cost +
          (E.topProjectedExecution hsteps D cut hcut).nonrootCount := by
  rw [E.cost_eq_stepCostSum]
  exact E.stepCostSum_le_projectedCostSums_add_topProjectedNonrootCount hsteps D cut hcut

/--
Projected-execution cost accounting with top exceptional projected costs
removed.  The bottom side is still a full projected cost.
-/
theorem cost_le_projectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.cost <=
      (E.bottomProjectedExecution hsteps D cut hcut).cost +
        (E.topProjectedExecution hsteps D cut hcut).consumableCost +
          (E.topProjectedExecution hsteps D cut hcut).nonrootCount := by
  rw [E.cost_eq_stepCostSum]
  exact
    E.stepCostSum_le_bottomProjectedCostSum_add_topConsumableCost_add_topProjectedNonrootCount
      hsteps D cut hcut

/-- Canonical-cut form of the projected-execution cost inequality. -/
theorem cost_le_canonicalProjectedExecutions_cost_add_topNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hsteps D).cost +
        (E.canonicalTopProjectedExecution hsteps D).cost +
          (E.canonicalTopProjectedExecution hsteps D).nonrootCount := by
  rw [E.cost_eq_stepCostSum]
  exact E.stepCostSum_le_projectedCostSums_add_topProjectedNonrootCount hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Canonical-cut projected-execution cost accounting with top exceptional costs
removed.
-/
theorem cost_le_canonicalProjectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hsteps D).cost +
        (E.canonicalTopProjectedExecution hsteps D).consumableCost +
          (E.canonicalTopProjectedExecution hsteps D).nonrootCount := by
  exact E.cost_le_projectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount
    hsteps D (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Paper-facing projected nonroot-count inequality for first-class projected
bottom/top executions.
-/
theorem projected_nonroot_count_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.bottomProjectedExecution hsteps D cut hcut).chargedCount +
        (E.topProjectedExecution hsteps D cut hcut).chargedCount <=
      E.nonrootCount := by
  simpa [RawCompressionPath.ProjectedCompressionExecution.chargedCount] using
    E.projectedExecutions_nonrootCount_add_le_nonrootCount hsteps D cut hcut

/-- Canonical-cut form of `projected_nonroot_count_le`. -/
theorem canonical_projected_nonroot_count_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    (E.canonicalBottomProjectedExecution hsteps D).chargedCount +
        (E.canonicalTopProjectedExecution hsteps D).chargedCount <=
      E.nonrootCount := by
  exact E.projected_nonroot_count_le hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/-- Rank-threshold specialization of the projected nonroot-count inequality. -/
theorem rankThreshold_projected_nonroot_count_le
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount <=
      E.nonrootCount := by
  exact E.canonical_projected_nonroot_count_le hE.1
    (E.rankThresholdDissectionFamily hE.1 s)

/--
Paper-facing projected source cost accounting.  The current finite projection
proof is stronger than this statement: it pays only the top projected
nonroot-count term, and the displayed bottom boundary-card budget is carried
for compatibility with the Seidel--Sharir main-lemma shape.
-/
theorem projected_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.cost <=
      (E.bottomProjectedExecution hsteps D cut hcut).projectedCost +
        (E.topProjectedExecution hsteps D cut hcut).projectedCost +
          E.bottomBoundaryCard D +
            (E.topProjectedExecution hsteps D cut hcut).chargedCount := by
  have hstrong :=
    E.cost_le_projectedExecutions_cost_add_topNonrootCount hsteps D cut hcut
  simp [RawCompressionPath.ProjectedCompressionExecution.projectedCost,
    RawCompressionPath.ProjectedCompressionExecution.chargedCount] at *
  omega

/-- Canonical-cut form of `projected_cost_main_lemma`. -/
theorem canonical_projected_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hsteps D).projectedCost +
        (E.canonicalTopProjectedExecution hsteps D).projectedCost +
          E.bottomBoundaryCard D +
            (E.canonicalTopProjectedExecution hsteps D).chargedCount := by
  exact E.projected_cost_main_lemma hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/--
Rank-threshold specialization of the projected main lemma with the stable
bottom side cardinality displayed as the paper-side `|X_b|` term.
-/
theorem rankThreshold_projected_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  have hmain :
      E.cost <=
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
            E.bottomBoundaryCard (E.rankThresholdDissectionFamily hE.1 s) +
              (E.canonicalTopProjectedExecution hE.1
                (E.rankThresholdDissectionFamily hE.1 s)).chargedCount :=
    E.canonical_projected_cost_main_lemma hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [E.rankThreshold_bottomBoundaryCard_eq_bottomFinset_card hE s i0] using hmain

/--
Rank-threshold projected accounting with the top exceptional projected cost
removed.  The remaining unconsumed projected term is the full bottom projected
cost.
-/
theorem rankThreshold_projected_consumable_cost_main_lemma
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  have hstrong :
      E.cost <=
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).cost +
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).nonrootCount :=
    E.cost_le_canonicalProjectedExecutions_bottomCost_add_topConsumableCost_add_topNonrootCount
      hE.1 (E.rankThresholdDissectionFamily hE.1 s)
  simp [RawCompressionPath.ProjectedCompressionExecution.projectedCost,
    RawCompressionPath.ProjectedCompressionExecution.chargedCount] at *
  omega

/--
Rank-threshold projected accounting with top exceptional projected cost removed
and the remaining top charge term consumed by execution length.
-/
theorem rankThreshold_projected_consumable_cost_main_lemma_add_length
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            m := by
  have hmain := E.rankThreshold_projected_consumable_cost_main_lemma hE s i0
  have hcharge :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount <= m :=
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount_le_length
  omega

/--
Rank-threshold projected main lemma with the top projected charge term consumed
by the execution length.  This is the projected-accounting form of the `+m`
term in the source shift recurrence.
-/
theorem rankThreshold_projected_cost_main_lemma_add_length
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).projectedCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            m := by
  have hmain := E.rankThreshold_projected_cost_main_lemma hE s i0
  have hcharge :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount <= m :=
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount_le_length
  omega

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
