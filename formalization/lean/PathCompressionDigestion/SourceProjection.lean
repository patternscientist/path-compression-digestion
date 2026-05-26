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

namespace RawRankedForest

variable {n r N : Nat} (F : RawRankedForest n r)

/--
Rank-threshold packing relative to an external vertex budget.  This is the
budgeted form needed for restricted/padded realizations: the forest itself may
have fewer vertices than the budget used to pay rank levels.
-/
def HasRankThresholdPackingWithBudget (N : Nat) : Prop :=
  forall s : Nat, (F.highRankFinset s).card * 2 ^ (s + 1) <= N

/-- Ordinary rank-threshold packing is the budgeted predicate at the exact size. -/
theorem hasRankThresholdPackingWithBudget_self
    (hpack : F.HasRankThresholdPacking) :
    F.HasRankThresholdPackingWithBudget n := by
  intro s
  exact hpack s

/-- Rank-threshold packing is invariant under pointwise rank equality. -/
theorem hasRankThresholdPacking_of_rankNat_eq
    (G : RawRankedForest n r)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (hpack : F.HasRankThresholdPacking) :
    G.HasRankThresholdPacking := by
  intro s
  have hset : G.highRankFinset s = F.highRankFinset s := by
    ext v
    simp [RawRankedForest.mem_highRankFinset, hrank v]
  simpa [hset] using hpack s

/-- Pad a forest into a larger finite vertex budget by adding rank-zero roots. -/
noncomputable def padRight
    {N : Nat}
    (hN : n <= N) :
    RawRankedForest N r where
  parent := fun v => by
    classical
    by_cases hv : v.val < n
    · exact ⟨(F.parent ⟨v.val, hv⟩).val, by omega⟩
    · exact v
  rank := fun v => by
    classical
    by_cases hv : v.val < n
    · exact F.rank ⟨v.val, hv⟩
    · exact ⟨0, Nat.succ_pos r⟩

/-- On original vertices, right-padding preserves rank. -/
theorem padRight_rankNat_of_lt
    {N : Nat}
    (hN : n <= N)
    (v : Fin N)
    (hv : v.val < n) :
    (F.padRight hN).rankNat v = F.rankNat ⟨v.val, hv⟩ := by
  simp [padRight, RawRankedForest.rankNat, hv]

/-- Added padding vertices have rank zero. -/
theorem padRight_rankNat_of_not_lt
    {N : Nat}
    (hN : n <= N)
    (v : Fin N)
    (hv : ¬ v.val < n) :
    (F.padRight hN).rankNat v = 0 := by
  simp [padRight, RawRankedForest.rankNat, hv]

/-- Right-padding preserves the rank-valid parent discipline. -/
theorem padRight_isRankValid
    {N : Nat}
    (hN : n <= N)
    (hF : F.IsRankValid) :
    (F.padRight hN).IsRankValid := by
  classical
  intro v hneq
  by_cases hv : v.val < n
  · let w : Fin n := ⟨v.val, hv⟩
    have hparent :
        (F.padRight hN).parent v =
          ⟨(F.parent w).val, by omega⟩ := by
      simp [padRight, hv, w]
    have hneqF : F.parent w ≠ w := by
      intro hw
      apply hneq
      apply Fin.ext
      simpa [hparent, w] using congrArg Fin.val hw
    have hlt := hF w hneqF
    have hparent_lt : ((F.padRight hN).parent v).val < n := by
      rw [hparent]
      exact (F.parent w).isLt
    calc
      (F.padRight hN).rankNat v
          = F.rankNat w := by
              simpa [w] using F.padRight_rankNat_of_lt hN v hv
      _ < F.rankNat (F.parent w) := hlt
      _ = (F.padRight hN).rankNat ((F.padRight hN).parent v) := by
              rw [F.padRight_rankNat_of_lt hN ((F.padRight hN).parent v) hparent_lt]
              simp [hparent, w]
  · have hparent : (F.padRight hN).parent v = v := by
      simp [padRight, hv]
    exact False.elim (hneq hparent)

/--
The high-rank vertices of a right-padded forest inject into the original
high-rank vertices; padding vertices have rank zero and never contribute.
-/
theorem padRight_highRankFinset_card_le
    {N : Nat}
    (hN : n <= N)
    (s : Nat) :
    ((F.padRight hN).highRankFinset s).card <= (F.highRankFinset s).card := by
  classical
  let emb :
      ((F.padRight hN).highRankFinset s) ↪ F.highRankFinset s := {
    toFun := fun v => by
      have hv_high :
          s < (F.padRight hN).rankNat v.1 :=
        (RawRankedForest.mem_highRankFinset (F.padRight hN) s v.1).1 v.2
      have hv_lt : v.1.val < n := by
        by_contra hv_not
        have hrank0 := F.padRight_rankNat_of_not_lt hN v.1 hv_not
        omega
      exact ⟨⟨v.1.val, hv_lt⟩,
        (RawRankedForest.mem_highRankFinset F s ⟨v.1.val, hv_lt⟩).2
          (by simpa [F.padRight_rankNat_of_lt hN v.1 hv_lt] using hv_high)⟩
    inj' := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun x : F.highRankFinset s => x.1.val) hab
  }
  have hle :
      Fintype.card ((F.padRight hN).highRankFinset s) <=
        Fintype.card (F.highRankFinset s) :=
    Fintype.card_le_of_injective emb emb.injective
  simpa [RawRankedForest.highRankFinset, Fintype.card_subtype] using hle

/--
Padding a budget-packed forest into its external budget gives ordinary
rank-threshold packing on the padded forest.
-/
theorem padRight_hasRankThresholdPacking
    {N : Nat}
    (hN : n <= N)
    (hpack : F.HasRankThresholdPackingWithBudget N) :
    (F.padRight hN).HasRankThresholdPacking := by
  intro s
  have hcard := F.padRight_highRankFinset_card_le hN s
  have hbudget := hpack s
  exact (Nat.mul_le_mul_right (2 ^ (s + 1)) hcard).trans hbudget

/-- A nonempty finite rank-valid parent forest has a root. -/
theorem exists_root_of_isRankValid
    (hF : F.IsRankValid)
    (hn : 0 < n) :
    Exists fun root : Fin n => F.parent root = root := by
  classical
  by_contra hno
  have hnonroot : forall v : Fin n, F.parent v ≠ v := by
    intro v hroot
    exact hno ⟨v, hroot⟩
  let v0 : Fin n := ⟨0, hn⟩
  have hstep :
      forall v : Fin n, F.rankNat v + 1 <= F.rankNat (F.parent v) := by
    intro v
    exact Nat.succ_le_of_lt (hF v (hnonroot v))
  have hiter :
      forall t : Nat, F.rankNat v0 + t <= F.rankNat (F.parentIter t v0) := by
    intro t
    induction t with
    | zero =>
        exact le_rfl
    | succ t ih =>
        calc
          F.rankNat v0 + (t + 1)
              = F.rankNat v0 + t + 1 := by omega
          _ <= F.rankNat (F.parentIter t v0) + 1 := by omega
          _ <= F.rankNat (F.parent (F.parentIter t v0)) :=
                hstep (F.parentIter t v0)
          _ = F.rankNat (F.parentIter (t + 1) v0) := by
                rw [F.parentIter_succ_eq_parent_parentIter]
  have hbig := hiter (r + 1)
  have hbound : F.rankNat (F.parentIter (r + 1) v0) <= r := by
    exact Nat.le_of_lt_succ ((F.rank (F.parentIter (r + 1) v0)).isLt)
  have hv0_bound : F.rankNat v0 <= r := by
    exact Nat.le_of_lt_succ ((F.rank v0).isLt)
  omega

end RawRankedForest

namespace RawDissection

variable {n r : Nat} {F : RawRankedForest n r}

/-- The inherited bottom rank strictly increases across non-root bottom-parent edges. -/
theorem bottomParent_rank_lt_of_not_root
    (D : RawDissection F)
    (hF : F.IsRankValid)
    (v : D.BottomNode)
    (hneq : D.bottomParent v ≠ v) :
    D.bottomRankNat v < D.bottomRankNat (D.bottomParent v) := by
  classical
  by_cases hparent : D.IsBottom (F.parent v.1)
  · have hraw_ne : F.parent v.1 ≠ v.1 := by
      intro hraw
      apply hneq
      apply Subtype.ext
      simpa [D.bottomParent_val_of_parent_bottom v hparent, hraw]
    have hlt : F.rankNat v.1 < F.rankNat (F.parent v.1) :=
      hF v.1 hraw_ne
    simpa [bottomRankNat, D.bottomParent_val_of_parent_bottom v hparent] using hlt
  · exfalso
    apply hneq
    apply Subtype.ext
    simp [bottomParent, hparent]

/-- The inherited top rank strictly increases across non-root top-parent edges. -/
theorem topParent_rank_lt_of_not_root
    (D : RawDissection F)
    (hF : F.IsRankValid)
    (v : D.TopNode)
    (hneq : D.topParent v ≠ v) :
    D.topRankNat v < D.topRankNat (D.topParent v) := by
  have hraw_ne : F.parent v.1 ≠ v.1 := by
    intro hraw
    apply hneq
    apply Subtype.ext
    simpa [topParent, hraw]
  simpa [topRankNat, topParent] using hF v.1 hraw_ne

/-- Top restricted vertices are equivalent to the displayed top finset. -/
def topNodeEquivTopFinset
    (D : RawDissection F) :
    D.TopNode ≃ D.topFinset := {
  toFun := fun v => ⟨v.1, (D.mem_topFinset v.1).2 v.2⟩,
  invFun := fun v => ⟨v.1, (D.mem_topFinset v.1).1 v.2⟩,
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/-- Canonical finite coordinates for the top restricted vertex type. -/
noncomputable def topNodeOrderEquivFin
    (D : RawDissection F) :
    D.TopNode ≃ Fin D.topFinset.card := by
  classical
  exact D.topNodeEquivTopFinset.trans (D.topFinset.orderIsoOfFin rfl).symm.toEquiv

/-- Canonical finite coordinates for the top restricted vertex type. -/
noncomputable def topNodeEquivFin
    (D : RawDissection F) :
    D.TopNode ≃ Fin D.topFinset.card :=
  D.topNodeOrderEquivFin

/--
The ordered top-coordinate value depends only on the displayed top finset, not
on the proof by which a vertex is presented as top.
-/
theorem topNodeOrderEquivFin_val_eq_of_topFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.topFinset = D'.topFinset)
    (x : Fin n)
    (hx : D.IsTop x)
    (hx' : D'.IsTop x) :
    (D.topNodeOrderEquivFin ⟨x, hx⟩).val =
      (D'.topNodeOrderEquivFin ⟨x, hx'⟩).val := by
  classical
  have hleft :
      (D.topNodeOrderEquivFin ⟨x, hx⟩).val =
        D.topFinset.sort.idxOf x := by
    simp [topNodeOrderEquivFin, topNodeEquivTopFinset,
      Finset.orderIsoOfFin_symm_apply]
  have hright :
      (D'.topNodeOrderEquivFin ⟨x, hx'⟩).val =
        D'.topFinset.sort.idxOf x := by
    simp [topNodeOrderEquivFin, topNodeEquivTopFinset,
      Finset.orderIsoOfFin_symm_apply]
  calc
    (D.topNodeOrderEquivFin ⟨x, hx⟩).val = D.topFinset.sort.idxOf x := hleft
    _ = D'.topFinset.sort.idxOf x := by simp [hset]
    _ = (D'.topNodeOrderEquivFin ⟨x, hx'⟩).val := hright.symm

/--
The public top-coordinate equivalence is ordered, so its coordinate value is
stable under equality of the displayed top finsets.
-/
theorem topNodeEquivFin_val_eq_of_topFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.topFinset = D'.topFinset)
    (x : Fin n)
    (hx : D.IsTop x)
    (hx' : D'.IsTop x) :
    (D.topNodeEquivFin ⟨x, hx⟩).val =
      (D'.topNodeEquivFin ⟨x, hx'⟩).val := by
  simpa [topNodeEquivFin] using
    D.topNodeOrderEquivFin_val_eq_of_topFinset_eq D' hset x hx hx'

/--
The inverse ordered top coordinate also depends only on the displayed top
finset.  This is the direction needed when two restricted forests have
definitionally different top-coordinate types but equal top membership.
-/
theorem topNodeEquivFin_symm_val_eq_of_topFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.topFinset = D'.topFinset)
    (a : Fin D.topFinset.card) :
    ((D.topNodeEquivFin).symm a).1 =
      ((D'.topNodeEquivFin).symm
        (Fin.cast (congrArg Finset.card hset) a)).1 := by
  classical
  apply Fin.ext
  simp [topNodeEquivFin, topNodeOrderEquivFin, topNodeEquivTopFinset,
    Finset.orderEmbOfFin_apply, hset]

/-- Bottom restricted vertices are equivalent to the displayed bottom finset. -/
def bottomNodeEquivBottomFinset
    (D : RawDissection F) :
    D.BottomNode ≃ D.bottomFinset := {
  toFun := fun v => ⟨v.1, (D.mem_bottomFinset v.1).2 v.2⟩,
  invFun := fun v => ⟨v.1, (D.mem_bottomFinset v.1).1 v.2⟩,
  left_inv := by
    intro v
    cases v
    rfl,
  right_inv := by
    intro v
    cases v
    rfl
}

/-- Canonical finite coordinates for the bottom restricted vertex type. -/
noncomputable def bottomNodeOrderEquivFin
    (D : RawDissection F) :
    D.BottomNode ≃ Fin D.bottomFinset.card := by
  classical
  exact D.bottomNodeEquivBottomFinset.trans
    (D.bottomFinset.orderIsoOfFin rfl).symm.toEquiv

/-- Canonical finite coordinates for the bottom restricted vertex type. -/
noncomputable def bottomNodeEquivFin
    (D : RawDissection F) :
    D.BottomNode ≃ Fin D.bottomFinset.card :=
  D.bottomNodeOrderEquivFin

/--
The ordered bottom-coordinate value depends only on the displayed bottom
finset, not on the proof by which a vertex is presented as bottom.
-/
theorem bottomNodeOrderEquivFin_val_eq_of_bottomFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.bottomFinset = D'.bottomFinset)
    (x : Fin n)
    (hx : D.IsBottom x)
    (hx' : D'.IsBottom x) :
    (D.bottomNodeOrderEquivFin ⟨x, hx⟩).val =
      (D'.bottomNodeOrderEquivFin ⟨x, hx'⟩).val := by
  classical
  have hleft :
      (D.bottomNodeOrderEquivFin ⟨x, hx⟩).val =
        D.bottomFinset.sort.idxOf x := by
    simp [bottomNodeOrderEquivFin, bottomNodeEquivBottomFinset,
      Finset.orderIsoOfFin_symm_apply]
  have hright :
      (D'.bottomNodeOrderEquivFin ⟨x, hx'⟩).val =
        D'.bottomFinset.sort.idxOf x := by
    simp [bottomNodeOrderEquivFin, bottomNodeEquivBottomFinset,
      Finset.orderIsoOfFin_symm_apply]
  calc
    (D.bottomNodeOrderEquivFin ⟨x, hx⟩).val = D.bottomFinset.sort.idxOf x := hleft
    _ = D'.bottomFinset.sort.idxOf x := by simp [hset]
    _ = (D'.bottomNodeOrderEquivFin ⟨x, hx'⟩).val := hright.symm

/--
The public bottom-coordinate equivalence is ordered, so its coordinate value is
stable under equality of the displayed bottom finsets.
-/
theorem bottomNodeEquivFin_val_eq_of_bottomFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.bottomFinset = D'.bottomFinset)
    (x : Fin n)
    (hx : D.IsBottom x)
    (hx' : D'.IsBottom x) :
    (D.bottomNodeEquivFin ⟨x, hx⟩).val =
      (D'.bottomNodeEquivFin ⟨x, hx'⟩).val := by
  simpa [bottomNodeEquivFin] using
    D.bottomNodeOrderEquivFin_val_eq_of_bottomFinset_eq D' hset x hx hx'

/--
The inverse ordered bottom coordinate also depends only on the displayed
bottom finset.
-/
theorem bottomNodeEquivFin_symm_val_eq_of_bottomFinset_eq
    {G : RawRankedForest n r}
    (D : RawDissection F)
    (D' : RawDissection G)
    (hset : D.bottomFinset = D'.bottomFinset)
    (a : Fin D.bottomFinset.card) :
    ((D.bottomNodeEquivFin).symm a).1 =
      ((D'.bottomNodeEquivFin).symm
        (Fin.cast (congrArg Finset.card hset) a)).1 := by
  classical
  apply Fin.ext
  simp [bottomNodeEquivFin, bottomNodeOrderEquivFin,
    bottomNodeEquivBottomFinset, Finset.orderEmbOfFin_apply, hset]

end RawDissection

namespace RankThresholdDissection

variable {n r : Nat} (F : RawRankedForest n r)

/-- Shifted top rank strictly increases across non-root top-parent edges. -/
theorem topParent_shiftedRank_lt_of_not_root
    (hF : F.IsRankValid)
    (s : Nat)
    (v : (dissection F hF s).TopNode)
    (hneq : (dissection F hF s).topParent v ≠ v) :
    topShiftedRank F hF s v <
      topShiftedRank F hF s ((dissection F hF s).topParent v) := by
  have hraw :
      F.rankNat v.1 <
        F.rankNat (((dissection F hF s).topParent v).1) := by
    simpa [RawDissection.topRankNat] using
      (dissection F hF s).topParent_rank_lt_of_not_root hF v hneq
  have hv : s + 1 <= F.rankNat v.1 := by
    exact Nat.succ_le_of_lt v.2
  unfold topShiftedRank
  omega

/--
Rank-threshold top coordinates are stable across forests with pointwise equal
rank functions.
-/
theorem topNodeEquivFin_val_eq_of_rankNat_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (x : Fin n)
    (hxF : (dissection F hF s).IsTop x)
    (hxG : (dissection G hG s).IsTop x) :
    (((dissection F hF s).topNodeEquivFin ⟨x, hxF⟩).val =
      ((dissection G hG s).topNodeEquivFin ⟨x, hxG⟩).val) := by
  classical
  have hset :
      (dissection F hF s).topFinset =
        (dissection G hG s).topFinset := by
    ext v
    simp [hrank v]
  exact (dissection F hF s).topNodeEquivFin_val_eq_of_topFinset_eq
    (dissection G hG s) hset x hxF hxG

/--
The inverse rank-threshold top coordinate is stable across forests with
pointwise equal rank functions, after casting along the induced cardinality
equality.
-/
theorem topNodeEquivFin_symm_val_eq_of_rankNat_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (a : Fin (dissection F hF s).topFinset.card) :
    let hset :
        (dissection F hF s).topFinset =
          (dissection G hG s).topFinset := by
        ext v
        simp [hrank v]
    (((dissection F hF s).topNodeEquivFin).symm a).1 =
      (((dissection G hG s).topNodeEquivFin).symm
        (Fin.cast (congrArg Finset.card hset) a)).1 := by
  classical
  intro hset
  exact (dissection F hF s).topNodeEquivFin_symm_val_eq_of_topFinset_eq
    (dissection G hG s) hset a

/-- Rank-threshold bottom coordinates are stable across forests with pointwise equal ranks. -/
theorem bottomNodeEquivFin_val_eq_of_rankNat_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (x : Fin n)
    (hxF : (dissection F hF s).IsBottom x)
    (hxG : (dissection G hG s).IsBottom x) :
    (((dissection F hF s).bottomNodeEquivFin ⟨x, hxF⟩).val =
      ((dissection G hG s).bottomNodeEquivFin ⟨x, hxG⟩).val) := by
  classical
  have hset :
      (dissection F hF s).bottomFinset =
        (dissection G hG s).bottomFinset := by
    ext v
    simp [hrank v]
  exact (dissection F hF s).bottomNodeEquivFin_val_eq_of_bottomFinset_eq
    (dissection G hG s) hset x hxF hxG

/--
The inverse rank-threshold bottom coordinate is stable across forests with
pointwise equal rank functions, after casting along the induced cardinality
equality.
-/
theorem bottomNodeEquivFin_symm_val_eq_of_rankNat_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (a : Fin (dissection F hF s).bottomFinset.card) :
    let hset :
        (dissection F hF s).bottomFinset =
          (dissection G hG s).bottomFinset := by
        ext v
        simp [hrank v]
    (((dissection F hF s).bottomNodeEquivFin).symm a).1 =
      (((dissection G hG s).bottomNodeEquivFin).symm
        (Fin.cast (congrArg Finset.card hset) a)).1 := by
  classical
  intro hset
  exact (dissection F hF s).bottomNodeEquivFin_symm_val_eq_of_bottomFinset_eq
    (dissection G hG s) hset a

/-- The rank-threshold top restricted forest in concrete `Fin |X_t|` coordinates. -/
noncomputable def topRestrictedForestFin
    (hF : F.IsRankValid)
    (s : Nat) :
    RawRankedForest (dissection F hF s).topFinset.card (r - s - 1) := by
  classical
  let D := dissection F hF s
  let e := D.topNodeEquivFin
  exact {
    parent := fun v => e (D.topParent (e.symm v))
    rank := fun v =>
      ⟨topShiftedRank F hF s (e.symm v),
        Nat.lt_succ_of_le (top_shifted_rank_le F hF s (e.symm v))⟩
  }

/-- The concrete top restricted forest preserves the shifted rank discipline. -/
theorem topRestrictedForestFin_isRankValid
    (hF : F.IsRankValid)
    (s : Nat) :
    (topRestrictedForestFin F hF s).IsRankValid := by
  classical
  intro v hneq
  let D := dissection F hF s
  let e := D.topNodeEquivFin
  let x : D.TopNode := e.symm v
  have hx_ne : D.topParent x ≠ x := by
    intro hx
    apply hneq
    have hparent :
        (topRestrictedForestFin F hF s).parent v = e (D.topParent x) := by
      simp [topRestrictedForestFin, D, e, x]
    calc
      (topRestrictedForestFin F hF s).parent v = e (D.topParent x) := hparent
      _ = e x := by rw [hx]
      _ = v := by simp [x, e]
  have hlt := topParent_shiftedRank_lt_of_not_root F hF s x hx_ne
  simpa [topRestrictedForestFin, D, e, x, RawRankedForest.rankNat] using hlt

/-- The rank-threshold bottom restricted forest in concrete `Fin |B_s|` coordinates. -/
noncomputable def bottomRestrictedForestFin
    (hF : F.IsRankValid)
    (s : Nat) :
    RawRankedForest (dissection F hF s).bottomFinset.card s := by
  classical
  let D := dissection F hF s
  let e := D.bottomNodeEquivFin
  exact {
    parent := fun v => e (D.bottomParent (e.symm v))
    rank := fun v =>
      ⟨F.rankNat (e.symm v).1,
        Nat.lt_succ_of_le (bottom_rank_le F hF s (e.symm v))⟩
  }

/-- The concrete bottom restricted forest preserves the inherited rank discipline. -/
theorem bottomRestrictedForestFin_isRankValid
    (hF : F.IsRankValid)
    (s : Nat) :
    (bottomRestrictedForestFin F hF s).IsRankValid := by
  classical
  intro v hneq
  let D := dissection F hF s
  let e := D.bottomNodeEquivFin
  let x : D.BottomNode := e.symm v
  have hx_ne : Not (D.bottomParent x = x) := by
    intro hx
    apply hneq
    have hparent :
        (bottomRestrictedForestFin F hF s).parent v = e (D.bottomParent x) := by
      simp [bottomRestrictedForestFin, D, e, x]
    calc
      (bottomRestrictedForestFin F hF s).parent v = e (D.bottomParent x) := hparent
      _ = e x := by rw [hx]
      _ = v := by simp [x, e]
  have hlt := D.bottomParent_rank_lt_of_not_root hF x hx_ne
  simpa [bottomRestrictedForestFin, D, e, x, RawRankedForest.rankNat,
    RawDissection.bottomRankNat] using hlt

/-- Bottom restricted forest parents are the bottom-parent map in bottom coordinates. -/
theorem bottomRestrictedForestFin_parent_of_bottomNode
    (hF : F.IsRankValid)
    (s : Nat)
    (v : (dissection F hF s).BottomNode) :
    let D := dissection F hF s
    let e := D.bottomNodeEquivFin
    (bottomRestrictedForestFin F hF s).parent (e v) = e (D.bottomParent v) := by
  classical
  intro D e
  simp [bottomRestrictedForestFin, D, e]

/--
The exact bottom restriction satisfies ordinary rank-threshold packing.  This
is the bottom-side counterpart to the budgeted top restriction.
-/
theorem bottomRestrictedForestFin_hasRankThresholdPacking
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (bottomRestrictedForestFin F hF s).HasRankThresholdPacking := by
  classical
  intro t
  let D := dissection F hF s
  let G := bottomRestrictedForestFin F hF s
  let e := D.bottomNodeEquivFin
  let Ht := G.highRankFinset t
  let Hb : Finset (Fin n) := Finset.univ.filter fun v => D.IsBottom v /\ t < F.rankNat v
  have hHb_eq :
      Hb = D.bottomFinset.filter fun v => t < F.rankNat v := by
    ext v
    simp [Hb]
  have hcard_eq : Ht.card = Hb.card := by
    let equiv : Ht ≃ Hb := {
      toFun := fun v => by
        let x : D.BottomNode := e.symm v.1
        have hv_high : t < G.rankNat v.1 :=
          (RawRankedForest.mem_highRankFinset G t v.1).1 v.2
        have hraw : t < F.rankNat x.1 := by
          simpa [G, bottomRestrictedForestFin, D, e, x,
            RawRankedForest.rankNat] using hv_high
        exact ⟨x.1, Finset.mem_filter.mpr ⟨by simp, x.2, hraw⟩⟩
      invFun := fun v => by
        let x : D.BottomNode :=
          ⟨v.1, (Finset.mem_filter.mp v.2).2.1⟩
        have hraw : t < F.rankNat x.1 := by
          simpa [x] using (Finset.mem_filter.mp v.2).2.2
        have hhigh : t < G.rankNat (e x) := by
          simpa [G, bottomRestrictedForestFin, D, e, x,
            RawRankedForest.rankNat] using hraw
        exact ⟨e x, (RawRankedForest.mem_highRankFinset G t (e x)).2 hhigh⟩
      left_inv := by
        intro v
        apply Subtype.ext
        simp [e]
      right_inv := by
        intro v
        apply Subtype.ext
        simp [e]
    }
    have hHt_card : Fintype.card Ht = Ht.card := by
      simpa [Ht, RawRankedForest.highRankFinset, Fintype.card_subtype]
    have hHb_card : Fintype.card Hb = Hb.card := by
      simpa [Hb, RawDissection.bottomFinset, Fintype.card_subtype]
    calc
      Ht.card = Fintype.card Ht := hHt_card.symm
      _ = Fintype.card Hb := Fintype.card_congr equiv
      _ = Hb.card := hHb_card
  calc
    Ht.card * 2 ^ (t + 1) = Hb.card * 2 ^ (t + 1) := by rw [hcard_eq]
    _ = (D.bottomFinset.filter fun v => t < F.rankNat v).card * 2 ^ (t + 1) := by
      rw [hHb_eq]
    _ <= D.bottomFinset.card := by
      simpa [D, Hb] using
        bottom_highRank_card_mul_pow_le_bottom_card F hF hpack s t

/-- The stable Seidel--Sharir top-side budget for a threshold cut. -/
def topRestrictedBudget (s : Nat) : Nat :=
  n / 2 ^ (s + 1)

/-- The external top budget has the same weighted size bound used in the shift. -/
theorem two_mul_topRestrictedBudget_mul_le
    (s g : Nat)
    (hg : g <= 2 ^ s) :
    2 * topRestrictedBudget (n := n) s * g <= n := by
  let B := topRestrictedBudget (n := n) s
  have hg2 : 2 * g <= 2 ^ (s + 1) := by
    calc
      2 * g <= 2 * 2 ^ s := Nat.mul_le_mul_left 2 hg
      _ = 2 ^ (s + 1) := by
            rw [Nat.pow_succ]
            ring
  have hdiv : B * 2 ^ (s + 1) <= n := by
    simpa [B, topRestrictedBudget] using Nat.div_mul_le_self n (2 ^ (s + 1))
  calc
    2 * B * g = B * (2 * g) := by ring
    _ <= B * 2 ^ (s + 1) := Nat.mul_le_mul_left B hg2
    _ <= n := hdiv

/-- The top restricted vertex count fits the external top-packing budget. -/
theorem topRestrictedForestFin_card_le_budget
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (dissection F hF s).topFinset.card <= topRestrictedBudget (n := n) s := by
  simpa [topRestrictedBudget] using
    top_card_le_div F hF s (topPacking_of_rankThresholdPacking F hF hpack s)

/--
The shifted top restriction satisfies rank-threshold packing with respect to
the external top budget `n / 2^(s+1)`.  This is the budgeted replacement for
the false exact-cardinality packing statement.
-/
theorem topRestrictedForestFin_hasRankThresholdPackingWithBudget
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (topRestrictedForestFin F hF s).HasRankThresholdPackingWithBudget
      (topRestrictedBudget (n := n) s) := by
  classical
  intro t
  let D := dissection F hF s
  let G := topRestrictedForestFin F hF s
  let e := D.topNodeEquivFin
  let Ht := G.highRankFinset t
  let Hamb := F.highRankFinset (s + t + 1)
  have hcard_le : Ht.card <= Hamb.card := by
    let emb : Ht ↪ Hamb := {
      toFun := fun v => by
        let x : D.TopNode := e.symm v.1
        have hv_high : t < G.rankNat v.1 :=
          (RawRankedForest.mem_highRankFinset G t v.1).1 v.2
        have hshift : t < topShiftedRank F hF s x := by
          simpa [G, topRestrictedForestFin, D, e, x, RawRankedForest.rankNat]
            using hv_high
        have hamb : s + t + 1 < F.rankNat x.1 := by
          have hx_top : s < F.rankNat x.1 := x.2
          unfold topShiftedRank at hshift
          omega
        exact ⟨x.1,
          (RawRankedForest.mem_highRankFinset F (s + t + 1) x.1).2 hamb⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        have hval : (e.symm a.1).1 = (e.symm b.1).1 := by
          simpa using congrArg Subtype.val hab
        have hx : e.symm a.1 = e.symm b.1 := Subtype.ext hval
        have hfin : a.1 = b.1 := by
          have heq := congrArg e hx
          simpa [e] using heq
        exact hfin
    }
    have hle : Fintype.card Ht <= Fintype.card Hamb :=
      Fintype.card_le_of_injective emb emb.injective
    simpa [Ht, Hamb, RawRankedForest.highRankFinset, Fintype.card_subtype] using hle
  have hamb_pack :
      Hamb.card * 2 ^ ((s + t + 1) + 1) <= n := by
    simpa [Hamb] using hpack (s + t + 1)
  have hpow_index : (s + t + 1) + 1 = s + t + 2 := by omega
  have hmul :
      Ht.card * 2 ^ (s + t + 2) <= n := by
    calc
      Ht.card * 2 ^ (s + t + 2)
          <= Hamb.card * 2 ^ (s + t + 2) :=
            Nat.mul_le_mul_right (2 ^ (s + t + 2)) hcard_le
      _ = Hamb.card * 2 ^ ((s + t + 1) + 1) := by rw [hpow_index]
      _ <= n := hamb_pack
  have hpos : 0 < 2 ^ (s + 1) := Nat.pow_pos (by norm_num : 0 < 2)
  apply (Nat.le_div_iff_mul_le hpos).2
  have hpows : 2 ^ (t + 1) * 2 ^ (s + 1) = 2 ^ (s + t + 2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    Ht.card * 2 ^ (t + 1) * 2 ^ (s + 1)
        = Ht.card * (2 ^ (t + 1) * 2 ^ (s + 1)) := by ring
    _ = Ht.card * 2 ^ (s + t + 2) := by rw [hpows]
    _ <= n := hmul

/-- The budget-padded shifted top restriction is rank-valid. -/
theorem topRestrictedForestFin_padded_isRankValid
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (topRestrictedForestFin F hF s).padRight
      (topRestrictedForestFin_card_le_budget F hF hpack s) |>.IsRankValid := by
  exact (topRestrictedForestFin F hF s).padRight_isRankValid
    (topRestrictedForestFin_card_le_budget F hF hpack s)
    (topRestrictedForestFin_isRankValid F hF s)

/--
Padding the shifted top restriction into the external top budget gives the
ordinary rank-threshold packing certificate required by source-valid forests.
-/
theorem topRestrictedForestFin_padded_hasRankThresholdPacking
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    (topRestrictedForestFin F hF s).padRight
      (topRestrictedForestFin_card_le_budget F hF hpack s) |>.HasRankThresholdPacking := by
  exact (topRestrictedForestFin F hF s).padRight_hasRankThresholdPacking
    (topRestrictedForestFin_card_le_budget F hF hpack s)
    (topRestrictedForestFin_hasRankThresholdPackingWithBudget F hF hpack s)

/--
Embedding a top restricted vertex into the padded top budget commutes with the
top parent map.
-/
theorem topRestrictedForestFin_padded_parent_of_topNode
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat)
    (v : (dissection F hF s).TopNode) :
    let D := dissection F hF s
    let G := topRestrictedForestFin F hF s
    let hN := topRestrictedForestFin_card_le_budget F hF hpack s
    let e := D.topNodeEquivFin
    (G.padRight hN).parent
        ⟨(e v).val, (e v).isLt.trans_le hN⟩ =
      ⟨(e (D.topParent v)).val,
        (e (D.topParent v)).isLt.trans_le hN⟩ := by
  classical
  intro D G hN e
  apply Fin.ext
  have hv : (e v).val < D.topFinset.card := (e v).isLt
  simp [RawRankedForest.padRight, topRestrictedForestFin, D, G, e, hv]

/--
Pointwise parent-coordinate compatibility for padded rank-threshold top
restrictions.  If ranks agree and `G.parent x` is a specified top vertex `y`
from the `F` coordinates, then the padded top restriction of `G` maps the
`F`-coordinate of `x` to the `F`-coordinate of `y`.
-/
theorem topRestrictedForestFin_padded_parent_eq_of_rankNat_eq_of_parent_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (hpackF : F.HasRankThresholdPacking)
    (hpackG : G.HasRankThresholdPacking)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (x y : (dissection F hF s).TopNode)
    (hparent : G.parent x.1 = y.1) :
    let Df := dissection F hF s
    let hNF := topRestrictedForestFin_card_le_budget F hF hpackF s
    let hNG := topRestrictedForestFin_card_le_budget G hG hpackG s
    let eF := Df.topNodeEquivFin
    ((topRestrictedForestFin G hG s).padRight hNG).parent
        ⟨(eF x).val, (eF x).isLt.trans_le hNF⟩ =
      ⟨(eF y).val, (eF y).isLt.trans_le hNF⟩ := by
  classical
  intro Df hNF hNG eF
  let Dg := dissection G hG s
  have hset : Df.topFinset = Dg.topFinset := by
    ext v
    simp [Df, Dg, hrank v]
  have hcard : Df.topFinset.card = Dg.topFinset.card :=
    congrArg Finset.card hset
  have hxG : Dg.IsTop x.1 := by
    simpa [Df, Dg, RankThresholdDissection.dissection_isTop, hrank x.1] using x.2
  have hyG : Dg.IsTop y.1 := by
    simpa [Df, Dg, RankThresholdDissection.dissection_isTop, hrank y.1] using y.2
  let axF : Fin Df.topFinset.card := eF x
  have haxG_lt : axF.val < Dg.topFinset.card := by omega
  let axG : Fin Dg.topFinset.card := ⟨axF.val, haxG_lt⟩
  have hcast : Fin.cast hcard axF = axG := by
    apply Fin.ext
    rfl
  have hrawx :
      ((Dg.topNodeEquivFin).symm axG).1 = x.1 := by
    have hsymm :=
      topNodeEquivFin_symm_val_eq_of_rankNat_eq
        F G hF hG s hrank axF
    have hxback : ((Df.topNodeEquivFin).symm axF).1 = x.1 := by
      simp [axF, eF]
    simpa [Df, Dg, hcast, hxback] using hsymm.symm
  have htopParent :
      Dg.topParent ((Dg.topNodeEquivFin).symm axG) = ⟨y.1, hyG⟩ := by
    apply Subtype.ext
    change G.parent (((Dg.topNodeEquivFin).symm axG).1) = y.1
    rw [hrawx]
    exact hparent
  apply Fin.ext
  simp [RawRankedForest.padRight, topRestrictedForestFin, Dg, haxG_lt,
    axF, axG, eF, htopParent]
  exact (topNodeEquivFin_val_eq_of_rankNat_eq
    F G hF hG s hrank y.1 y.2 hyG).symm

/--
Padded rank-threshold top restrictions are literally equal when ranks agree
pointwise and top-side raw parents agree on the first forest's top vertices.
-/
theorem topRestrictedForestFin_padded_eq_of_rankNat_eq_of_top_parent_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (hpackF : F.HasRankThresholdPacking)
    (hpackG : G.HasRankThresholdPacking)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (hparent :
      forall x : (dissection F hF s).TopNode, G.parent x.1 = F.parent x.1) :
    (topRestrictedForestFin G hG s).padRight
        (topRestrictedForestFin_card_le_budget G hG hpackG s) =
      (topRestrictedForestFin F hF s).padRight
        (topRestrictedForestFin_card_le_budget F hF hpackF s) := by
  classical
  let Df := dissection F hF s
  let Dg := dissection G hG s
  let hNF := topRestrictedForestFin_card_le_budget F hF hpackF s
  let hNG := topRestrictedForestFin_card_le_budget G hG hpackG s
  have hset : Df.topFinset = Dg.topFinset := by
    ext v
    simp [Df, Dg, hrank v]
  have hcard : Df.topFinset.card = Dg.topFinset.card :=
    congrArg Finset.card hset
  refine congrArg₂
    (fun parent rank =>
      ({ parent := parent, rank := rank } :
        RawRankedForest (topRestrictedBudget (n := n) s) (r - s - 1)))
    ?_ ?_ <;> funext v
  · by_cases hvF : v.val < Df.topFinset.card
    · have hvG : v.val < Dg.topFinset.card := by omega
      let aF : Fin Df.topFinset.card := ⟨v.val, hvF⟩
      let aG : Fin Dg.topFinset.card := ⟨v.val, hvG⟩
      have hcast : Fin.cast hcard aF = aG := by
        apply Fin.ext
        rfl
      have hraw :
          ((Df.topNodeEquivFin).symm aF).1 =
            ((Dg.topNodeEquivFin).symm aG).1 := by
        have hsymm :=
          topNodeEquivFin_symm_val_eq_of_rankNat_eq
            F G hF hG s hrank aF
        simpa [Df, Dg, hcast] using hsymm
      have hparent_raw :
          G.parent (((Dg.topNodeEquivFin).symm aG).1) =
            F.parent (((Df.topNodeEquivFin).symm aF).1) := by
        rw [← hraw]
        exact hparent ((Df.topNodeEquivFin).symm aF)
      apply Fin.ext
      simp [topRestrictedForestFin, Df, Dg, hvF, hvG]
      simpa [Df, Dg, aF, aG, RawDissection.topParent, hraw, hparent_raw] using
        (topNodeEquivFin_val_eq_of_rankNat_eq
        F G hF hG s hrank
        (F.parent (((Df.topNodeEquivFin).symm aF).1))
        (by
          simpa [Df, RawDissection.topParent] using
            (Df.topParent ((Df.topNodeEquivFin).symm aF)).2)
        (by
          have htopG :
              Dg.IsTop (G.parent (((Dg.topNodeEquivFin).symm aG).1)) :=
            (Dg.topParent ((Dg.topNodeEquivFin).symm aG)).2
          rw [hparent_raw] at htopG
          simpa [Dg] using htopG)).symm
    · have hvG : ¬ v.val < Dg.topFinset.card := by omega
      simp [Df, Dg, hvF, hvG]
  · by_cases hvF : v.val < Df.topFinset.card
    · have hvG : v.val < Dg.topFinset.card := by omega
      let aF : Fin Df.topFinset.card := ⟨v.val, hvF⟩
      let aG : Fin Dg.topFinset.card := ⟨v.val, hvG⟩
      have hcast : Fin.cast hcard aF = aG := by
        apply Fin.ext
        rfl
      have hraw :
          ((Df.topNodeEquivFin).symm aF).1 =
            ((Dg.topNodeEquivFin).symm aG).1 := by
        have hsymm :=
          topNodeEquivFin_symm_val_eq_of_rankNat_eq
            F G hF hG s hrank aF
        simpa [Df, Dg, hcast] using hsymm
      apply Fin.ext
      simp [topRestrictedForestFin, Df, Dg, hvF, hvG]
      unfold topShiftedRank
      rw [← hraw]
      exact congrArg (fun q => q - (s + 1))
        (hrank (((Df.topNodeEquivFin).symm aF).1))
    · have hvG : ¬ v.val < Dg.topFinset.card := by omega
      simp [Df, Dg, hvF, hvG]

/--
Padded rank-threshold top restrictions have the same shifted rank function
whenever the ambient forests have pointwise equal ranks.
-/
theorem topRestrictedForestFin_padded_rank_eq_of_rankNat_eq
    (F G : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hG : G.IsRankValid)
    (hpackF : F.HasRankThresholdPacking)
    (hpackG : G.HasRankThresholdPacking)
    (s : Nat)
    (hrank : forall v : Fin n, G.rankNat v = F.rankNat v)
    (v : Fin (topRestrictedBudget (n := n) s)) :
    ((topRestrictedForestFin G hG s).padRight
        (topRestrictedForestFin_card_le_budget G hG hpackG s)).rank v =
      ((topRestrictedForestFin F hF s).padRight
        (topRestrictedForestFin_card_le_budget F hF hpackF s)).rank v := by
  classical
  let Df := dissection F hF s
  let Dg := dissection G hG s
  have hset : Df.topFinset = Dg.topFinset := by
    ext v
    simp [Df, Dg, hrank v]
  have hcard : Df.topFinset.card = Dg.topFinset.card :=
    congrArg Finset.card hset
  apply Fin.ext
  by_cases hvF : v.val < Df.topFinset.card
  · have hvG : v.val < Dg.topFinset.card := by omega
    let aF : Fin Df.topFinset.card := ⟨v.val, hvF⟩
    let aG : Fin Dg.topFinset.card := ⟨v.val, hvG⟩
    have hcast : Fin.cast hcard aF = aG := by
      apply Fin.ext
      rfl
    have hraw :
        ((Df.topNodeEquivFin).symm aF).1 =
          ((Dg.topNodeEquivFin).symm aG).1 := by
      have hsymm :=
        topNodeEquivFin_symm_val_eq_of_rankNat_eq
          F G hF hG s hrank aF
      simpa [Df, Dg, hcast] using hsymm
    simp [RawRankedForest.padRight, topRestrictedForestFin, Df, Dg, hvF, hvG]
    unfold topShiftedRank
    rw [← hraw]
    exact congrArg (fun q => q - (s + 1))
      (hrank (((Df.topNodeEquivFin).symm aF).1))
  · have hvG : ¬ v.val < Dg.topFinset.card := by omega
    simp [RawRankedForest.padRight, Df, Dg, hvF, hvG]

/--
The ambient rank-threshold packing invariant does not automatically localize
to the top restricted forest with shifted ranks.  This is the concrete reason
the remaining top recurrence-consumption proof needs an additional source
realization/packing argument rather than mere top-side cardinality transport.
-/
theorem exists_topRestrictedForestFin_without_rankThresholdPacking :
    Exists fun F : RawRankedForest 8 3 =>
      Exists fun hF : F.IsRankValid =>
        F.HasRankThresholdPacking /\
          Not ((topRestrictedForestFin F hF 0).HasRankThresholdPacking) := by
  classical
  let v0 : Fin 8 := ⟨0, by norm_num⟩
  let v1 : Fin 8 := ⟨1, by norm_num⟩
  let F : RawRankedForest 8 3 := {
    parent := fun v => v
    rank := fun v =>
      if v.val = 0 then ⟨1, by norm_num⟩
      else if v.val = 1 then ⟨3, by norm_num⟩
      else ⟨0, by norm_num⟩
  }
  have hF : F.IsRankValid := by
    intro v hv
    exact False.elim (hv rfl)
  have hpack : F.HasRankThresholdPacking := by
    intro s
    by_cases hs0 : s = 0
    · subst s
      have hset : F.highRankFinset 0 = {v0, v1} := by
        ext v
        fin_cases v <;> simp [F, v0, v1, RawRankedForest.highRankFinset,
          RawRankedForest.rankNat]
      rw [hset]
      simp [v0, v1]
    · by_cases hs1 : s = 1
      · subst s
        have hset : F.highRankFinset 1 = {v1} := by
          ext v
          fin_cases v <;> simp [F, v1, RawRankedForest.highRankFinset,
            RawRankedForest.rankNat]
        rw [hset]
        norm_num
      · by_cases hs2 : s = 2
        · subst s
          have hset : F.highRankFinset 2 = {v1} := by
            ext v
            fin_cases v <;> simp [F, v1, RawRankedForest.highRankFinset,
              RawRankedForest.rankNat]
          rw [hset]
          norm_num
        · have hs_ge : 3 <= s := by omega
          have hs0' : s ≠ 0 := by omega
          have hset : F.highRankFinset s = ∅ := by
            ext v
            fin_cases v <;> simp [F, RawRankedForest.highRankFinset,
              RawRankedForest.rankNat, hs_ge, hs0']
          rw [hset]
          simp
  have hnot :
      Not ((topRestrictedForestFin F hF 0).HasRankThresholdPacking) := by
    intro htopPack
    let D := dissection F hF 0
    let G := topRestrictedForestFin F hF 0
    let e := D.topNodeEquivFin
    let topv1 : D.TopNode := ⟨v1, by
      change 0 < F.rankNat v1
      norm_num [F, v1, RawRankedForest.rankNat]⟩
    have htopcard : D.topFinset.card = 2 := by
      have hset : D.topFinset = {v0, v1} := by
        ext v
        fin_cases v <;> simp [D, F, v0, v1, dissection, topPred,
          RawDissection.topFinset, RawDissection.IsTop, RawRankedForest.rankNat]
      rw [hset]
      simp [v0, v1]
    have hmem :
        e topv1 ∈ G.highRankFinset 1 := by
      apply (RawRankedForest.mem_highRankFinset G 1 (e topv1)).2
      change 1 < topShiftedRank F hF 0 (e.symm (e topv1))
      rw [show e.symm (e topv1) = topv1 by simp [e]]
      simp [topv1, topShiftedRank, F, v1, RawRankedForest.rankNat]
    have hcard_pos : 1 <= (G.highRankFinset 1).card := by
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨e topv1, hmem⟩)
    have hbad := htopPack 1
    have hfour_le : 4 <= (G.highRankFinset 1).card * 2 ^ (1 + 1) := by
      have hmul := Nat.mul_le_mul_right (2 ^ (1 + 1)) hcard_pos
      norm_num at hmul ⊢
      exact hmul
    have hambient :
        (G.highRankFinset 1).card * 2 ^ (1 + 1) <= 2 := by
      simpa [G, topRestrictedForestFin, D, htopcard] using hbad
    omega
  exact ⟨F, hF, hpack, hnot⟩

end RankThresholdDissection

namespace RawCompressionPath

namespace ProjectedPathSegment

variable {alpha : Type*} {parent : alpha -> alpha}

/-- Last slot of a nonempty projected path segment. -/
def lastIndex (S : ProjectedPathSegment alpha parent) (hlen : 0 < S.len) : Fin S.len :=
  { val := S.len - 1, isLt := by omega }

/--
Realize a nonempty projected segment as an ordinary path over a padded
coordinate budget.  Inactive slots are filled with the projected target, so
compressed vertices are exactly the embedded projected slots strictly before
the target.
-/
noncomputable def toPaddedPath
    (S : ProjectedPathSegment alpha parent)
    {N : Nat}
    (embed : alpha -> Fin N)
    (hlen : S.len <= N)
    (hpos : 0 < S.len) :
    RawCompressionPath N := {
  len := ⟨S.len, by omega⟩
  node := fun j =>
    if hj : j.val < S.len then embed (S.node ⟨j.val, hj⟩)
    else embed (S.node (S.lastIndex hpos))
  target := embed (S.node (S.lastIndex hpos))
}

/--
Compressed vertices of the padded realization are exactly the embedded
projected segment vertices strictly before the projected target.
-/
theorem toPaddedPath_isCompressedVertex_iff
    (S : ProjectedPathSegment alpha parent)
    {N : Nat}
    (embed : alpha -> Fin N)
    (hlen : S.len <= N)
    (hpos : 0 < S.len)
    (v : Fin N) :
    (S.toPaddedPath embed hlen hpos).IsCompressedVertex v <->
      Exists fun i : Fin S.len =>
        i.val + 1 < S.len /\ embed (S.node i) = v := by
  constructor
  · intro hcomp
    rcases hcomp with ⟨j, hj, hnode⟩
    have hjS : j.val + 1 < S.len := by
      simpa [toPaddedPath] using hj
    have hjlt : j.val < S.len := by omega
    refine ⟨⟨j.val, hjlt⟩, hjS, ?_⟩
    simpa [toPaddedPath, hjlt] using hnode
  · intro hcomp
    rcases hcomp with ⟨i, hi, hv⟩
    have hiN : i.val < N + 1 := by omega
    let j : Fin (N + 1) := ⟨i.val, hiN⟩
    refine ⟨j, ?_, ?_⟩
    · simpa [toPaddedPath, j] using hi
    · simpa [toPaddedPath, j] using hv

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

/--
If a projected segment ever reaches a self-parent vertex, all later slots in
the segment stay at that vertex.
-/
theorem node_eq_of_parent_self_of_le
    (S : ProjectedPathSegment alpha parent)
    {i j : Fin S.len}
    (hij : i.val <= j.val)
    (hself : parent (S.node i) = S.node i) :
    S.node j = S.node i := by
  rcases Nat.exists_eq_add_of_le hij with ⟨d, hd⟩
  revert i j
  induction d with
  | zero =>
      intro i j _hij hself hd
      have hvals : i.val = j.val := by omega
      exact (congrArg S.node (Fin.ext hvals)).symm
  | succ d ih =>
      intro i j _hij hself hd
      let mid : Fin S.len := ⟨i.val + d, by omega⟩
      have hi_mid : i.val <= mid.val := by
        simp [mid]
      have hmid_val : mid.val = i.val + d := rfl
      have hmid_j : mid.val + 1 = j.val := by
        simp [mid]
        omega
      have hnode_mid : S.node mid = S.node i :=
        ih hi_mid hself hmid_val
      have hparent_mid : parent (S.node mid) = S.node mid := by
        rw [hnode_mid, hself]
      have hchain : parent (S.node mid) = S.node j :=
        S.parent_chain hmid_j
      calc
        S.node j = parent (S.node mid) := hchain.symm
        _ = S.node mid := hparent_mid
        _ = S.node i := hnode_mid

/-- Ranks are nondecreasing along a projected path when they are nondecreasing
along the projected parent map. -/
theorem rank_le_of_le
    (S : ProjectedPathSegment alpha parent)
    (rank : alpha -> Nat)
    (hparent_le : forall v : alpha, rank v <= rank (parent v))
    {i j : Fin S.len}
    (hij : i.val <= j.val) :
    rank (S.node i) <= rank (S.node j) := by
  rcases Nat.exists_eq_add_of_le hij with ⟨d, hd⟩
  revert i j
  induction d with
  | zero =>
      intro i j _hij hd
      have hvals : i.val = j.val := by omega
      have hfin : i = j := Fin.ext hvals
      simpa [hfin]
  | succ d ih =>
      intro i j _hij hd
      let mid : Fin S.len := ⟨i.val + d, by omega⟩
      have hi_mid : i.val <= mid.val := by
        simp [mid]
      have hmid_val : mid.val = i.val + d := rfl
      have hmid_j : mid.val + 1 = j.val := by
        simp [mid]
        omega
      have hle_mid : rank (S.node i) <= rank (S.node mid) :=
        ih hi_mid hmid_val
      have hstep : parent (S.node mid) = S.node j :=
        S.parent_chain hmid_j
      exact hle_mid.trans (by simpa [hstep] using hparent_le (S.node mid))

/--
On a projected nonroot path, any rank function that strictly increases across
non-root parent edges strictly increases between earlier and later slots.
-/
theorem rank_lt_of_lt_of_nonroot
    (S : ProjectedPathSegment alpha parent)
    (rank : alpha -> Nat)
    (hparent_lt : forall v : alpha, parent v ≠ v -> rank v < rank (parent v))
    (hnonroot : S.IsNonrootPath)
    {i j : Fin S.len}
    (hij : i.val < j.val) :
    rank (S.node i) < rank (S.node j) := by
  rcases hnonroot with ⟨hlen, hlast_ne⟩
  let next : Fin S.len := ⟨i.val + 1, by omega⟩
  have hi_next : i.val + 1 = next.val := rfl
  have hnext_le_j : next.val <= j.val := by
    simp [next]
    omega
  have hparent_i : parent (S.node i) = S.node next :=
    S.parent_chain hi_next
  have hnot_self : parent (S.node i) ≠ S.node i := by
    intro hself
    let last := S.lastIndex hlen
    have hi_last : i.val <= last.val := by
      simp [last, lastIndex]
      omega
    have hlast_node : S.node last = S.node i :=
      S.node_eq_of_parent_self_of_le hi_last hself
    have hparent_last : parent (S.node last) = S.node last := by
      rw [hlast_node, hself]
    exact hlast_ne hparent_last
  have hlt_next : rank (S.node i) < rank (S.node next) := by
    simpa [hparent_i] using hparent_lt (S.node i) hnot_self
  have hparent_le : forall v : alpha, rank v <= rank (parent v) := by
    intro v
    by_cases hv : parent v = v
    · rw [hv]
    · exact le_of_lt (hparent_lt v hv)
  have hle_j : rank (S.node next) <= rank (S.node j) :=
    S.rank_le_of_le rank hparent_le hnext_le_j
  exact hlt_next.trans_le hle_j

/--
A nonroot projected path whose node ranks all lie in `0..B` has at most `B`
edges.
-/
theorem edgeCost_le_rankBound_of_nonroot
    (S : ProjectedPathSegment alpha parent)
    (rank : alpha -> Nat)
    (B : Nat)
    (hparent_lt : forall v : alpha, parent v ≠ v -> rank v < rank (parent v))
    (hrank_bound : forall i : Fin S.len, rank (S.node i) <= B)
    (hnonroot : S.IsNonrootPath) :
    S.edgeCost <= B := by
  classical
  let rankFin : Fin S.len -> Fin (B + 1) := fun i =>
    ⟨rank (S.node i), Nat.lt_succ_of_le (hrank_bound i)⟩
  have hinj : Function.Injective rankFin := by
    intro i j hij
    apply Fin.ext
    by_cases hlt : i.val < j.val
    · have hrank_lt : rank (S.node i) < rank (S.node j) :=
        S.rank_lt_of_lt_of_nonroot rank hparent_lt hnonroot hlt
      have hrank_eq : rank (S.node i) = rank (S.node j) := by
        exact congrArg Fin.val hij
      omega
    · by_cases hgt : j.val < i.val
      · have hrank_lt : rank (S.node j) < rank (S.node i) :=
          S.rank_lt_of_lt_of_nonroot rank hparent_lt hnonroot hgt
        have hrank_eq : rank (S.node i) = rank (S.node j) := by
          exact congrArg Fin.val hij
        omega
      · omega
  have hcard :
      Fintype.card (Fin S.len) <= Fintype.card (Fin (B + 1)) :=
    Fintype.card_le_of_injective rankFin hinj
  have hlen_le : S.len <= B + 1 := by
    simpa using hcard
  unfold edgeCost
  omega

/-- A nonroot projected path has no repeated vertices. -/
theorem node_injective_of_nonroot
    (S : ProjectedPathSegment alpha parent)
    (rank : alpha -> Nat)
    (hparent_lt : forall v : alpha, parent v ≠ v -> rank v < rank (parent v))
    (hnonroot : S.IsNonrootPath) :
    Function.Injective S.node := by
  intro i j hij
  apply Fin.ext
  by_cases hlt : i.val < j.val
  · have hrank_lt : rank (S.node i) < rank (S.node j) :=
      S.rank_lt_of_lt_of_nonroot rank hparent_lt hnonroot hlt
    rw [hij] at hrank_lt
    exact False.elim ((Nat.lt_irrefl _) hrank_lt)
  · by_cases hgt : j.val < i.val
    · have hrank_lt : rank (S.node j) < rank (S.node i) :=
        S.rank_lt_of_lt_of_nonroot rank hparent_lt hnonroot hgt
      rw [hij] at hrank_lt
      exact False.elim ((Nat.lt_irrefl _) hrank_lt)
    · omega

/-- A nonroot projected path has length at most its ambient finite vertex set. -/
theorem len_le_card_of_nonroot
    [Fintype alpha]
    (S : ProjectedPathSegment alpha parent)
    (rank : alpha -> Nat)
    (hparent_lt : forall v : alpha, parent v ≠ v -> rank v < rank (parent v))
    (hnonroot : S.IsNonrootPath) :
    S.len <= Fintype.card alpha := by
  have hinj : Function.Injective S.node :=
    S.node_injective_of_nonroot rank hparent_lt hnonroot
  have hcard :
      Fintype.card (Fin S.len) <= Fintype.card alpha :=
    Fintype.card_le_of_injective S.node hinj
  simpa using hcard

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

/-- Charged projected steps have nonroot indicator one. -/
theorem nonrootIndicator_eq_one_of_charged
    (S : ProjectedCompressionStep alpha)
    (h : S.IsCharged) :
    S.nonrootIndicator = 1 := by
  have hseg : S.path.IsNonrootPath := by
    simpa [IsCharged, IsNonrootPath] using h
  exact S.path.nonrootIndicator_eq_one_of_nonroot hseg

/-- Uncharged projected steps have nonroot indicator zero. -/
theorem nonrootIndicator_eq_zero_of_not_charged
    (S : ProjectedCompressionStep alpha)
    (h : Not S.IsCharged) :
    S.nonrootIndicator = 0 := by
  classical
  have hnot : Not S.path.IsNonrootPath := by
    intro hseg
    exact h (by simpa [IsCharged, IsNonrootPath] using hseg)
  unfold nonrootIndicator ProjectedPathSegment.nonrootIndicator
  rw [if_neg hnot]

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

/-- A zero nonroot indicator forces zero recurrence-consumable cost. -/
theorem consumableCost_eq_zero_of_nonrootIndicator_eq_zero
    (S : ProjectedCompressionStep alpha)
    (h : S.nonrootIndicator = 0) :
    S.consumableCost = 0 := by
  classical
  by_cases hcharged : S.IsCharged
  · have hseg : S.path.IsNonrootPath := by
      simpa [IsCharged, IsNonrootPath] using hcharged
    have hnonroot : S.nonrootIndicator = 1 := by
      unfold nonrootIndicator
      exact S.path.nonrootIndicator_eq_one_of_nonroot hseg
    omega
  · exact S.consumableCost_eq_zero_of_not_charged hcharged

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

/-- Consumable projected cost is bounded by total projected step cost. -/
theorem consumableCost_le_cost (S : ProjectedCompressionStep alpha) :
    S.consumableCost <= S.cost := by
  classical
  by_cases h : S.IsCharged <;> simp [consumableCost, h]

/-- Exceptional projected cost is bounded by total projected step cost. -/
theorem exceptionalCost_le_cost (S : ProjectedCompressionStep alpha) :
    S.exceptionalCost <= S.cost := by
  classical
  by_cases h : S.IsCharged <;> simp [exceptionalCost, h]

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

/-- Finset of charged projected execution slots. -/
noncomputable def chargedFinset (E : ProjectedCompressionExecution m) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => (E.step i).IsCharged

@[simp]
theorem mem_chargedFinset
    (E : ProjectedCompressionExecution m)
    (i : Fin m) :
    i ∈ E.chargedFinset ↔ (E.step i).IsCharged := by
  classical
  simp [chargedFinset]

/-- The charged slot finset has cardinality `chargedCount`. -/
theorem chargedFinset_card_eq_chargedCount
    (E : ProjectedCompressionExecution m) :
    E.chargedFinset.card = E.chargedCount := by
  classical
  unfold chargedFinset chargedCount nonrootCount
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : (E.step i).IsCharged
  · rw [if_pos h, (E.step i).nonrootIndicator_eq_one_of_charged h]
  · rw [if_neg h, (E.step i).nonrootIndicator_eq_zero_of_not_charged h]

/--
Increasing enumeration of the charged projected execution slots.

This is the compacted slot map needed to build ordinary executions over
`Fin E.chargedCount` from charged projected slots.
-/
noncomputable def chargedSlot
    (E : ProjectedCompressionExecution m) :
    Fin E.chargedCount → Fin m :=
  E.chargedFinset.orderEmbOfFin E.chargedFinset_card_eq_chargedCount

@[simp]
theorem chargedSlot_mem_chargedFinset
    (E : ProjectedCompressionExecution m)
    (q : Fin E.chargedCount) :
    E.chargedSlot q ∈ E.chargedFinset := by
  simpa [chargedSlot] using
    Finset.orderEmbOfFin_mem E.chargedFinset
      E.chargedFinset_card_eq_chargedCount q

/-- Every compacted charged slot is charged. -/
theorem chargedSlot_isCharged
    (E : ProjectedCompressionExecution m)
    (q : Fin E.chargedCount) :
    (E.step (E.chargedSlot q)).IsCharged := by
  exact (E.mem_chargedFinset (E.chargedSlot q)).1
    (E.chargedSlot_mem_chargedFinset q)

/-- The compacted charged-slot enumeration is strictly increasing. -/
theorem chargedSlot_strictMono
    (E : ProjectedCompressionExecution m) :
    StrictMono E.chargedSlot := by
  intro q q' hlt
  exact (E.chargedFinset.orderEmbOfFin
    E.chargedFinset_card_eq_chargedCount).strictMono hlt

/--
There are no charged projected slots strictly between adjacent entries of the
compacted charged-slot enumeration.
-/
theorem not_isCharged_of_between_chargedSlot_succ
    (E : ProjectedCompressionExecution m)
    {q q' : Fin E.chargedCount}
    (hqq' : q.val + 1 = q'.val)
    (i : Fin m)
    (hleft : (E.chargedSlot q).val < i.val)
    (hright : i.val < (E.chargedSlot q').val) :
    Not (E.step i).IsCharged := by
  intro hcharged
  have hi_mem : i ∈ E.chargedFinset := (E.mem_chargedFinset i).2 hcharged
  have hi_range :
      i ∈ Set.range
        (E.chargedFinset.orderEmbOfFin E.chargedFinset_card_eq_chargedCount) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi_mem
  rcases hi_range with ⟨p, hp⟩
  have hp_eq : E.chargedSlot p = i := by
    simpa [chargedSlot] using hp
  have hq_lt_p : q.val < p.val := by
    by_contra hnot
    have hp_le_q : p.val <= q.val := by omega
    by_cases hpq : p.val = q.val
    · have hp_fin : p = q := Fin.ext hpq
      subst p
      rw [hp_eq] at hleft
      exact (Nat.lt_irrefl _) hleft
    · have hp_lt_q : p.val < q.val := by omega
      have hslot_lt :
          (E.chargedSlot p).val < (E.chargedSlot q).val :=
        (E.chargedSlot_strictMono hp_lt_q)
      rw [hp_eq] at hslot_lt
      omega
  have hp_lt_q' : p.val < q'.val := by
    by_contra hnot
    have hq'_le_p : q'.val <= p.val := by omega
    by_cases hpq' : p.val = q'.val
    · have hp_fin : p = q' := Fin.ext hpq'
      subst p
      rw [hp_eq] at hright
      exact (Nat.lt_irrefl _) hright
    · have hq'_lt_p : q'.val < p.val := by omega
      have hslot_lt :
          (E.chargedSlot q').val < (E.chargedSlot p).val :=
        (E.chargedSlot_strictMono hq'_lt_p)
      rw [hp_eq] at hslot_lt
      omega
  omega

/-- Dependent projected execution obtained by keeping only charged slots. -/
noncomputable def chargedSubexecution
    (E : ProjectedCompressionExecution m) :
    ProjectedCompressionExecution E.chargedCount where
  vertex := fun q => E.vertex (E.chargedSlot q)
  step := fun q => E.step (E.chargedSlot q)

/-- The charged subexecution has exactly the consumable cost of the original. -/
theorem chargedSubexecution_cost_eq_consumableCost
    (E : ProjectedCompressionExecution m) :
    E.chargedSubexecution.cost = E.consumableCost := by
  classical
  have hcost :
      E.chargedSubexecution.cost =
        Finset.sum E.chargedFinset (fun i => (E.step i).cost) := by
    let emb :=
      (E.chargedFinset.orderEmbOfFin
        E.chargedFinset_card_eq_chargedCount).toEmbedding
    calc
      E.chargedSubexecution.cost
          = ∑ q : Fin E.chargedCount, (E.step (E.chargedSlot q)).cost := by
              rfl
      _ = Finset.sum (Finset.map emb (Finset.univ : Finset (Fin E.chargedCount)))
            (fun i => (E.step i).cost) := by
              rw [Finset.sum_map]
              rfl
      _ = Finset.sum E.chargedFinset (fun i => (E.step i).cost) := by
              rw [Finset.map_orderEmbOfFin_univ]
  have hconsume :
      E.consumableCost =
        Finset.sum E.chargedFinset (fun i => (E.step i).cost) := by
    unfold consumableCost chargedFinset
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hcharged : (E.step i).IsCharged
    · simp [RawCompressionPath.ProjectedCompressionStep.consumableCost, hcharged]
    · simp [RawCompressionPath.ProjectedCompressionStep.consumableCost, hcharged]
  exact hcost.trans hconsume.symm

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

/-- If no projected slot is charged, no recurrence-consumable cost remains. -/
theorem consumableCost_eq_zero_of_chargedCount_eq_zero
    (E : ProjectedCompressionExecution m)
    (hcount : E.chargedCount = 0) :
    E.consumableCost = 0 := by
  classical
  unfold consumableCost
  apply Finset.sum_eq_zero
  intro i hi
  have hle :
      (E.step i).nonrootIndicator <= E.chargedCount := by
    unfold chargedCount nonrootCount
    exact Finset.single_le_sum
      (by intro j _hj; exact Nat.zero_le ((E.step j).nonrootIndicator)) hi
  have hzero : (E.step i).nonrootIndicator = 0 := by
    omega
  exact (E.step i).consumableCost_eq_zero_of_nonrootIndicator_eq_zero hzero

/-- Positive recurrence-consumable cost forces a positive charged count. -/
theorem chargedCount_pos_of_consumableCost_pos
    (E : ProjectedCompressionExecution m)
    (hcost : 0 < E.consumableCost) :
    0 < E.chargedCount := by
  by_contra hnot
  have hzero : E.chargedCount = 0 := Nat.eq_zero_of_not_pos hnot
  have hcost_zero := E.consumableCost_eq_zero_of_chargedCount_eq_zero hzero
  omega

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

/-- A charged bottom rank-threshold projection has at most `s` edges. -/
theorem bottomProjectionSegment_edgeCost_le_rankThreshold
    {n r : Nat}
    {F : RawRankedForest n r}
    (hF : F.IsRankValid)
    (s : Nat)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut (RankThresholdDissection.dissection F hF s) cut)
    (hnonroot :
      (P.bottomProjectionSegment
        (RankThresholdDissection.dissection F hF s) hchain cut hcut).IsNonrootPath) :
    (P.bottomProjectionSegment
      (RankThresholdDissection.dissection F hF s) hchain cut hcut).edgeCost <= s := by
  let D := RankThresholdDissection.dissection F hF s
  exact (P.bottomProjectionSegment D hchain cut hcut).edgeCost_le_rankBound_of_nonroot
    D.bottomRankNat s
    (fun v hneq => D.bottomParent_rank_lt_of_not_root hF v hneq)
    (fun i => by
      exact RankThresholdDissection.bottom_rank_le F hF s
        ((P.bottomProjectionSegment D hchain cut hcut).node i))
    hnonroot

/--
A charged top rank-threshold projection has at most `r - s - 1` edges after
shifting ranks down by the threshold boundary.
-/
theorem topProjectionSegment_edgeCost_le_rankThreshold
    {n r : Nat}
    {F : RawRankedForest n r}
    (hF : F.IsRankValid)
    (s : Nat)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut (RankThresholdDissection.dissection F hF s) cut)
    (hnonroot :
      (P.topProjectionSegment
        (RankThresholdDissection.dissection F hF s) hchain cut hcut).IsNonrootPath) :
    (P.topProjectionSegment
      (RankThresholdDissection.dissection F hF s) hchain cut hcut).edgeCost <=
        r - s - 1 := by
  let D := RankThresholdDissection.dissection F hF s
  exact (P.topProjectionSegment D hchain cut hcut).edgeCost_le_rankBound_of_nonroot
    (RankThresholdDissection.topShiftedRank F hF s) (r - s - 1)
    (fun v hneq =>
      RankThresholdDissection.topParent_shiftedRank_lt_of_not_root F hF s v hneq)
    (fun i => by
      exact RankThresholdDissection.top_shifted_rank_le F hF s
        ((P.topProjectionSegment D hchain cut hcut).node i))
    hnonroot

/--
On a valid source nonroot path, every compressed vertex has smaller rank than
the old parent of the target.  This is the rank-validity fact behind the
standard one-step compression after-forest.
-/
theorem rankNat_lt_parent_target_of_compressedVertex_of_nonroot
    {n r : Nat}
    {F : RawRankedForest n r}
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (hnonroot : P.IsNonrootPath F)
    {v : Fin n}
    (hcomp : P.IsCompressedVertex v) :
    F.rankNat v < F.rankNat (F.parent P.target) := by
  rcases hcomp with ⟨i, hi_before_target, hnode⟩
  have hlen_one : 1 <= P.len.val := by
    omega
  let last := P.lastIndex hlen_one
  have hlast_active : last.val < P.len.val := P.lastIndex_active hlen_one
  have hi_lt_last : i.val < last.val := by
    simp [last, RawCompressionPath.lastIndex]
    omega
  have htarget : P.node last = P.target :=
    hvalid.2.2.2 last (P.lastIndex_succ hlen_one)
  have hrank_to_target :
      F.rankNat v < F.rankNat P.target := by
    have hlt :=
      P.rankNat_lt_of_lt_active_of_nonroot hvalid hnonroot hi_lt_last hlast_active
    simpa [hnode, htarget] using hlt
  have htarget_parent :
      F.rankNat P.target < F.rankNat (F.parent P.target) :=
    hvalid.1 P.target hnonroot
  exact hrank_to_target.trans htarget_parent

/--
The standard after-forest obtained by compressing a valid source nonroot path
is a valid raw compression step.  This packages the generic semantic
construction used by padded top-step realizations.
-/
theorem exists_valid_step_of_valid_nonroot_path
    {n r : Nat}
    (F : RawRankedForest n r)
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (hnonroot : P.IsNonrootPath F) :
    Exists fun S : RawCompressionStep n r =>
      S.before = F /\ S.path = P /\ S.IsValid /\ S.cost = P.cost := by
  classical
  let A : RawRankedForest n r := {
    parent := fun v =>
      if P.IsCompressedVertex v then F.parent P.target else F.parent v
    rank := F.rank
  }
  let S : RawCompressionStep n r := {
    before := F
    after := A
    path := P
  }
  have hA_rank : A.IsRankValid := by
    intro v hneq
    by_cases hcomp : P.IsCompressedVertex v
    · have hlt :=
        P.rankNat_lt_parent_target_of_compressedVertex_of_nonroot
          hvalid hnonroot hcomp
      simpa [A, RawRankedForest.rankNat, hcomp] using hlt
    · have hneqF : F.parent v ≠ v := by
        intro hv
        apply hneq
        simp [A, hcomp, hv]
      have hlt := hvalid.1 v hneqF
      simpa [A, RawRankedForest.rankNat, hcomp] using hlt
  have hS_valid : S.IsValid := by
    refine ⟨hvalid, hA_rank, ?hrank, ?hroot, ?hnonroot, ?hunchanged⟩
    · intro v
      rfl
    · intro hroot
      exact False.elim (hnonroot hroot)
    · intro _hnonroot v hcomp
      simp [S, A, hcomp]
    · intro v hnot
      simp [S, A, hnot]
  have hS_cost : S.cost = P.cost := by
    unfold S RawCompressionStep.cost RawCompressionPath.sourceCost
    rw [if_neg]
    intro hroot
    exact hnonroot hroot
  exact ⟨S, rfl, rfl, hS_valid, hS_cost⟩

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

/-- A charged bottom rank-threshold projected step has at most `s` consumable edges. -/
theorem bottomProjectedStep_consumableCost_le_rankThreshold
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (s : Nat)
    (cut : Nat)
    (hcut :
      S.path.HasDissectionCut
        (RankThresholdDissection.dissection S.before hS.1.1 s) cut) :
    (S.bottomProjectedStep
      (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).consumableCost <=
      s := by
  classical
  let D := RankThresholdDissection.dissection S.before hS.1.1 s
  let B := S.bottomProjectedStep D hS cut hcut
  by_cases hcharged : B.IsCharged
  · have hseg :
        (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).IsNonrootPath := by
      simpa [B, RawCompressionStep.bottomProjectedStep,
        RawCompressionPath.ProjectedCompressionStep.IsCharged,
        RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
    have hcost :
        (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost <= s :=
      S.path.bottomProjectionSegment_edgeCost_le_rankThreshold
        hS.1.1 s hS.1.2.2.1 cut hcut hseg
    rw [B.consumableCost_eq_cost_of_charged hcharged]
    simpa [B, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hcost
  · rw [B.consumableCost_eq_zero_of_not_charged hcharged]
    omega

/--
Charged-count form of the bottom rank-threshold projected-step range bound.
-/
theorem bottomProjectedStep_consumableCost_le_rankThreshold_mul_indicator
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (s : Nat)
    (cut : Nat)
    (hcut :
      S.path.HasDissectionCut
        (RankThresholdDissection.dissection S.before hS.1.1 s) cut) :
    (S.bottomProjectedStep
      (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).consumableCost <=
      s *
        (S.bottomProjectedStep
          (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).nonrootIndicator := by
  classical
  let D := RankThresholdDissection.dissection S.before hS.1.1 s
  let B := S.bottomProjectedStep D hS cut hcut
  by_cases hcharged : B.IsCharged
  · have hcost := S.bottomProjectedStep_consumableCost_le_rankThreshold hS s cut hcut
    have hind : B.nonrootIndicator = 1 := by
      have hseg : B.path.IsNonrootPath := by
        simpa [RawCompressionPath.ProjectedCompressionStep.IsCharged,
          RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
      exact B.path.nonrootIndicator_eq_one_of_nonroot hseg
    simpa [B, D, hind] using hcost
  · rw [B.consumableCost_eq_zero_of_not_charged hcharged]
    omega

/--
A charged top rank-threshold projected step has at most `r - s - 1` consumable
edges after shifting top ranks down by the threshold boundary.
-/
theorem topProjectedStep_consumableCost_le_rankThreshold
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (s : Nat)
    (cut : Nat)
    (hcut :
      S.path.HasDissectionCut
        (RankThresholdDissection.dissection S.before hS.1.1 s) cut) :
    (S.topProjectedStep
      (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).consumableCost <=
      r - s - 1 := by
  classical
  let D := RankThresholdDissection.dissection S.before hS.1.1 s
  let T := S.topProjectedStep D hS cut hcut
  by_cases hcharged : T.IsCharged
  · have hseg :
        (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).IsNonrootPath := by
      simpa [T, RawCompressionStep.topProjectedStep,
        RawCompressionPath.ProjectedCompressionStep.IsCharged,
        RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
    have hcost :
        (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost <= r - s - 1 :=
      S.path.topProjectionSegment_edgeCost_le_rankThreshold
        hS.1.1 s hS.1.2.2.1 cut hcut hseg
    rw [T.consumableCost_eq_cost_of_charged hcharged]
    simpa [T, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hcost
  · rw [T.consumableCost_eq_zero_of_not_charged hcharged]
    omega

/-- Charged-count form of the top rank-threshold projected-step range bound. -/
theorem topProjectedStep_consumableCost_le_rankThreshold_mul_indicator
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (s : Nat)
    (cut : Nat)
    (hcut :
      S.path.HasDissectionCut
        (RankThresholdDissection.dissection S.before hS.1.1 s) cut) :
    (S.topProjectedStep
      (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).consumableCost <=
      (r - s - 1) *
        (S.topProjectedStep
          (RankThresholdDissection.dissection S.before hS.1.1 s) hS cut hcut).nonrootIndicator := by
  classical
  let D := RankThresholdDissection.dissection S.before hS.1.1 s
  let T := S.topProjectedStep D hS cut hcut
  by_cases hcharged : T.IsCharged
  · have hcost := S.topProjectedStep_consumableCost_le_rankThreshold hS s cut hcut
    have hind : T.nonrootIndicator = 1 := by
      have hseg : T.path.IsNonrootPath := by
        simpa [RawCompressionPath.ProjectedCompressionStep.IsCharged,
          RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
      exact T.path.nonrootIndicator_eq_one_of_nonroot hseg
    simpa [T, D, hind] using hcost
  · rw [T.consumableCost_eq_zero_of_not_charged hcharged]
    omega

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
Top projected recurrence-consumable cost is always dominated by the original
source step cost.  Source rootpaths contribute no top consumable cost; source
nonrootpaths dominate the top projected suffix by length.
-/
theorem topProjectedStep_consumableCost_le_cost
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    (S.topProjectedStep D hS cut hcut).consumableCost <= S.cost := by
  classical
  let T := S.topProjectedStep D hS cut hcut
  by_cases hnonroot : S.path.IsNonrootPath S.before
  · have htop_cost :
        T.cost = T.consumableCost := by
      simpa [T] using
        S.topProjectedStep_cost_eq_consumableCost_of_source_nonroot
          D hS cut hcut hnonroot
    have hlen :
        (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).len <=
          S.path.len.val := by
      simpa [RawCompressionPath.topProjectionSegment] using
        S.path.topProjectionLength_le_len D cut hcut
    have hcost_le_segment :
        (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost <=
          S.path.cost := by
      unfold RawCompressionPath.ProjectedPathSegment.edgeCost
        RawCompressionPath.cost
      omega
    have hcost_le :
        T.cost <= S.path.cost := by
      simpa [T, RawCompressionStep.topProjectedStep,
        RawCompressionPath.ProjectedCompressionStep.cost] using hcost_le_segment
    have hstep_cost : S.cost = S.path.cost := by
      unfold RawCompressionStep.cost RawCompressionPath.sourceCost
      rw [if_neg]
      intro hroot
      exact hnonroot hroot
    rw [← htop_cost, hstep_cost]
    exact hcost_le
  · have hsource_zero : S.nonrootIndicator = 0 := by
      unfold RawCompressionStep.nonrootIndicator
      rw [if_neg hnonroot]
    have hproj :=
      S.projected_nonrootIndicators_add_le_nonrootIndicator D hS cut hcut
    have hTzero : T.nonrootIndicator = 0 := by
      have hle0 :
          (S.bottomProjectedStep D hS cut hcut).nonrootIndicator +
              T.nonrootIndicator <= 0 := by
        simpa [T, hsource_zero] using hproj
      omega
    rw [T.consumableCost_eq_zero_of_nonrootIndicator_eq_zero hTzero]
    exact Nat.zero_le _

/--
An uncharged top projected step leaves the top restricted parent map unchanged.
This is the local identity lemma needed before a charged-slot-only top
execution can skip root-like top projections.
-/
theorem topProjectedStep_afterParent_eq_beforeParent_of_not_charged
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnot : Not (S.topProjectedStep D hS cut hcut).IsCharged) :
    (S.topProjectedStep D hS cut hcut).afterParent =
      (S.topProjectedStep D hS cut hcut).beforeParent := by
  funext v
  apply Subtype.ext
  change S.after.parent v.1 = S.before.parent v.1
  by_cases hroot : S.path.IsRootPath S.before
  · exact congrFun (hS.2.2.2.1 hroot) v.1
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v.1
    · exfalso
      rcases hcomp with ⟨q, hq, hqnode⟩
      have hq_active : q.val < S.path.len.val := by omega
      have hcut_le_q : cut <= q.val := by
        by_contra hnotle
        have hq_lt_cut : q.val < cut := Nat.lt_of_not_ge hnotle
        have hbottom : D.IsBottom (S.path.node q) :=
          hcut.2.1 q hq_active hq_lt_cut
        rw [hqnode] at hbottom
        exact hbottom v.2
      have hcut_lt : cut < S.path.len.val := by omega
      have ht_nonroot :
          (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).IsNonrootPath :=
        S.path.topProjectionSegment_isNonrootPath_of_source_nonroot
          D hS.1.2.2.1 hS.1.2.2.2 hnonroot cut hcut hcut_lt
      have ht_charged : (S.topProjectedStep D hS cut hcut).IsCharged := by
        simpa [RawCompressionStep.topProjectedStep,
          RawCompressionPath.ProjectedCompressionStep.IsCharged,
          RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using ht_nonroot
      exact hnot ht_charged
    · exact hS.2.2.2.2.2 v.1 hcomp

/--
A zero-cost top projected step is identity on the top restricted parent map.
This covers the charged-but-zero-cost case: a one-vertex nonroot top suffix
carries a projected charge but compresses no top vertex.
-/
theorem topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hcost : (S.topProjectedStep D hS cut hcut).cost = 0) :
    (S.topProjectedStep D hS cut hcut).afterParent =
      (S.topProjectedStep D hS cut hcut).beforeParent := by
  funext v
  apply Subtype.ext
  change S.after.parent v.1 = S.before.parent v.1
  by_cases hroot : S.path.IsRootPath S.before
  · exact congrFun (hS.2.2.2.1 hroot) v.1
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v.1
    · exfalso
      rcases hcomp with ⟨q, hq, hqnode⟩
      have hq_active : q.val < S.path.len.val := by omega
      have hcut_le_q : cut <= q.val := by
        by_contra hnot
        have hq_lt_cut : q.val < cut := Nat.lt_of_not_ge hnot
        have hbottom : D.IsBottom (S.path.node q) :=
          hcut.2.1 q hq_active hq_lt_cut
        rw [hqnode] at hbottom
        exact hbottom v.2
      have htop_len_two : 2 <= S.path.topProjectionLength D cut hcut := by
        simp [RawCompressionPath.topProjectionLength]
        omega
      have hcost_pos :
          0 < (S.topProjectedStep D hS cut hcut).cost := by
        unfold RawCompressionStep.topProjectedStep
          RawCompressionPath.ProjectedCompressionStep.cost
          RawCompressionPath.ProjectedPathSegment.edgeCost
        simp [RawCompressionPath.topProjectionSegment,
          RawCompressionPath.topProjectionLength]
        omega
      omega
    · exact hS.2.2.2.2.2 v.1 hcomp

/--
A bottom projected step with no source-relevant boundary event leaves the bottom
restricted parent map unchanged.  The only compressed bottom vertex that can
remain when there is no lower bottom-prefix edge is the last bottom vertex
before a nonempty top suffix; both before and after bottom parents are then
truncated to the vertex itself.
-/
theorem bottomProjectedStep_afterParent_eq_beforeParent_of_no_sourceBoundary
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnotBoundary :
      Not (S.path.IsNonrootPath S.before /\
        Exists fun q : Fin (n + 1) => q.val + 1 < cut)) :
    (S.bottomProjectedStep D hS cut hcut).afterParent =
      (S.bottomProjectedStep D hS cut hcut).beforeParent := by
  funext v
  apply Subtype.ext
  change (S.afterBottomParent D hS v).1 = (D.bottomParent v).1
  classical
  by_cases hroot : S.path.IsRootPath S.before
  · have hparent_eq :
        S.after.parent v.1 = S.before.parent v.1 := by
      exact congrFun (hS.2.2.2.1 hroot) v.1
    by_cases hb : D.IsBottom (S.before.parent v.1)
    · have hb_after : D.IsBottom (S.after.parent v.1) := by
        simpa [hparent_eq] using hb
      have hleft :
          (S.afterBottomParent D hS v).1 = S.after.parent v.1 :=
        S.afterBottomParent_val_of_parent_bottom D hS v hb_after
      have hright :
          (D.bottomParent v).1 = S.before.parent v.1 :=
        D.bottomParent_val_of_parent_bottom v hb
      rw [hleft, hright, hparent_eq]
    · have ht : D.IsTop (S.before.parent v.1) := by
        unfold RawDissection.IsBottom at hb
        exact Decidable.not_not.mp hb
      have ht_after : D.IsTop (S.after.parent v.1) := by
        simpa [hparent_eq] using ht
      have hleft :
          (S.afterBottomParent D hS v).1 = v.1 :=
        S.afterBottomParent_val_of_parent_top D hS v ht_after
      have hright :
          (D.bottomParent v).1 = v.1 :=
        D.bottomParent_val_of_parent_top v ht
      rw [hleft, hright]
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v.1
    · rcases hcomp with ⟨q, hq, hqnode⟩
      have hq_active : q.val < S.path.len.val := by omega
      by_cases hq_boundary : q.val + 1 < cut
      · exact False.elim (hnotBoundary ⟨hnonroot, ⟨q, hq_boundary⟩⟩)
      · have hq_succ_ge_cut : cut <= q.val + 1 := Nat.le_of_not_gt hq_boundary
        by_cases hq_lt_cut : q.val < cut
        · have hq_succ_eq_cut : q.val + 1 = cut := by omega
          have hcut_lt_len : cut < S.path.len.val := by omega
          let qnext : Fin (n + 1) := ⟨q.val + 1, by
            have hlen_le : S.path.len.val <= n + 1 :=
              Nat.le_of_lt_succ S.path.len.isLt
            omega⟩
          have hqnext_active : qnext.val < S.path.len.val := by
            simp [qnext]
            omega
          have hqnext_cut : cut <= qnext.val := by
            simp [qnext, hq_succ_eq_cut]
          have hqnext_top : D.IsTop (S.path.node qnext) :=
            hcut.2.2 qnext hqnext_active hqnext_cut
          have hparent_eq_next :
              S.before.parent (S.path.node q) = S.path.node qnext :=
            hS.1.2.2.1 q qnext (by simp [qnext]) hqnext_active
          have hbefore_top : D.IsTop (S.before.parent v.1) := by
            rw [← hqnode, hparent_eq_next]
            exact hqnext_top
          have hright :
              (D.bottomParent v).1 = v.1 :=
            D.bottomParent_val_of_parent_top v hbefore_top
          have hlen_one : 1 <= S.path.len.val :=
            Nat.le_trans (by norm_num : 1 <= 2) hS.1.2.1
          let last := S.path.lastIndex hlen_one
          have hlast_active : last.val < S.path.len.val :=
            S.path.lastIndex_active hlen_one
          have hcut_last : cut <= last.val := by
            simp [last, RawCompressionPath.lastIndex]
            omega
          have hlast_top : D.IsTop (S.path.node last) :=
            hcut.2.2 last hlast_active hcut_last
          have hlast_target : S.path.node last = S.path.target :=
            hS.1.2.2.2 last (S.path.lastIndex_succ hlen_one)
          have htarget_top : D.IsTop S.path.target := by
            simpa [hlast_target] using hlast_top
          have htarget_parent_top :
              D.IsTop (S.before.parent S.path.target) :=
            D.parent_top htarget_top
          have hafter_parent_eq :
              S.after.parent v.1 = S.before.parent S.path.target := by
            exact hS.2.2.2.2.1 hnonroot v.1 ⟨q, hq, hqnode⟩
          have hafter_top : D.IsTop (S.after.parent v.1) := by
            rw [hafter_parent_eq]
            exact htarget_parent_top
          have hleft :
              (S.afterBottomParent D hS v).1 = v.1 :=
            S.afterBottomParent_val_of_parent_top D hS v hafter_top
          rw [hleft, hright]
        · have hq_ge_cut : cut <= q.val := Nat.le_of_not_gt hq_lt_cut
          have hq_top : D.IsTop (S.path.node q) :=
            hcut.2.2 q hq_active hq_ge_cut
          rw [hqnode] at hq_top
          exact False.elim (v.2 hq_top)
    · have hparent_eq :
        S.after.parent v.1 = S.before.parent v.1 :=
        hS.2.2.2.2.2 v.1 hcomp
      by_cases hb : D.IsBottom (S.before.parent v.1)
      · have hb_after : D.IsBottom (S.after.parent v.1) := by
          simpa [hparent_eq] using hb
        have hleft :
            (S.afterBottomParent D hS v).1 = S.after.parent v.1 :=
          S.afterBottomParent_val_of_parent_bottom D hS v hb_after
        have hright :
            (D.bottomParent v).1 = S.before.parent v.1 :=
          D.bottomParent_val_of_parent_bottom v hb
        rw [hleft, hright, hparent_eq]
      · have ht : D.IsTop (S.before.parent v.1) := by
          unfold RawDissection.IsBottom at hb
          exact Decidable.not_not.mp hb
        have ht_after : D.IsTop (S.after.parent v.1) := by
          simpa [hparent_eq] using ht
        have hleft :
            (S.afterBottomParent D hS v).1 = v.1 :=
          S.afterBottomParent_val_of_parent_top D hS v ht_after
        have hright :
            (D.bottomParent v).1 = v.1 :=
          D.bottomParent_val_of_parent_top v ht
        rw [hleft, hright]

/-- If the top side is empty, the top projected step has no consumable cost. -/
theorem topProjectedStep_consumableCost_eq_zero_of_topFinset_card_eq_zero
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hcard : D.topFinset.card = 0) :
    (S.topProjectedStep D hS cut hcut).consumableCost = 0 := by
  classical
  let T := S.topProjectedStep D hS cut hcut
  have htop_len_zero :
      S.path.topProjectionLength D cut hcut = 0 := by
    by_contra hne
    have hpos : 0 < S.path.topProjectionLength D cut hcut :=
      Nat.pos_of_ne_zero hne
    let q : Fin (S.path.topProjectionLength D cut hcut) := ⟨0, hpos⟩
    have hmem :
        S.path.node (S.path.topProjectionIndex D cut hcut q) ∈ D.topFinset := by
      exact (D.mem_topFinset _).2 (S.path.topProjectionNode D cut hcut q).2
    have hempty : D.topFinset = ∅ := Finset.card_eq_zero.mp hcard
    rw [hempty] at hmem
    simp at hmem
  have hpath_len : T.path.len = 0 := by
    simpa [T, RawCompressionStep.topProjectedStep,
      RawCompressionPath.topProjectionSegment] using htop_len_zero
  have hind : T.nonrootIndicator = 0 := by
    unfold RawCompressionPath.ProjectedCompressionStep.nonrootIndicator
    exact T.path.nonrootIndicator_eq_zero_of_len_eq_zero hpath_len
  exact T.consumableCost_eq_zero_of_nonrootIndicator_eq_zero hind

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
Bottom exceptional projected cost that is relevant to the original source
cost.  Source rootpaths have zero source cost, so their bottom projected
exceptions are deliberately ignored.
-/
noncomputable def sourceRelevantBottomExceptionalCost
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) : Nat := by
  classical
  exact if S.path.IsNonrootPath S.before then
    (S.bottomProjectedStep D hS cut hcut).exceptionalCost
  else
    0

@[simp]
theorem sourceRelevantBottomExceptionalCost_eq_exceptional_of_nonroot
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnonroot : S.path.IsNonrootPath S.before) :
    S.sourceRelevantBottomExceptionalCost D hS cut hcut =
      (S.bottomProjectedStep D hS cut hcut).exceptionalCost := by
  simp [sourceRelevantBottomExceptionalCost, hnonroot]

@[simp]
theorem sourceRelevantBottomExceptionalCost_eq_zero_of_not_nonroot
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnot : Not (S.path.IsNonrootPath S.before)) :
    S.sourceRelevantBottomExceptionalCost D hS cut hcut = 0 := by
  simp [sourceRelevantBottomExceptionalCost, hnot]

@[simp]
theorem sourceRelevantBottomExceptionalCost_eq_zero_of_root
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hroot : S.path.IsRootPath S.before) :
    S.sourceRelevantBottomExceptionalCost D hS cut hcut = 0 := by
  apply S.sourceRelevantBottomExceptionalCost_eq_zero_of_not_nonroot
  intro hnonroot
  exact hnonroot hroot

/--
In a source-nonroot bottom exceptional event, every raw slot contributing a
bottom-prefix edge is rewired to a top parent.  This is the local charging
fact behind the remaining global injection into the stable bottom side.
-/
theorem sourceRelevantBottomException_after_parent_top_of_index
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut)
    (hnonroot : S.path.IsNonrootPath S.before)
    (hnotCharged : Not (S.bottomProjectedStep D hS cut hcut).IsCharged)
    (q : Fin (n + 1))
    (hq : q.val + 1 < cut) :
    D.IsTop (S.after.parent (S.path.node q)) := by
  classical
  rcases hS with
    ⟨hpath, _hafterRank, _hrank, _hroot_step, hnonroot_step, _hunchanged⟩
  have hq_compressed : S.path.IsCompressedVertex (S.path.node q) := by
    refine ⟨q, ?_, rfl⟩
    exact lt_of_lt_of_le hq hcut.1
  have hrewire :
      S.after.parent (S.path.node q) = S.before.parent S.path.target :=
    hnonroot_step hnonroot (S.path.node q) hq_compressed
  have htarget_parent_top : D.IsTop (S.before.parent S.path.target) := by
    by_cases hcut_lt : cut < S.path.len.val
    · have hlen_one : 1 <= S.path.len.val := by
        exact Nat.le_trans (by norm_num : 1 <= 2) hpath.2.1
      let last := S.path.lastIndex hlen_one
      have hlast_active : last.val < S.path.len.val :=
        S.path.lastIndex_active hlen_one
      have hcut_last : cut <= last.val := by
        simp [last, RawCompressionPath.lastIndex]
        omega
      have hlast_top : D.IsTop (S.path.node last) :=
        hcut.2.2 last hlast_active hcut_last
      have hlast_target : S.path.node last = S.path.target :=
        hpath.2.2.2 last (S.path.lastIndex_succ hlen_one)
      have htarget_top : D.IsTop S.path.target := by
        simpa [hlast_target] using hlast_top
      exact D.parent_top htarget_top
    · have hcut_eq : cut = S.path.len.val := by
        exact le_antisymm hcut.1 (Nat.le_of_not_gt hcut_lt)
      have hcut_pos : 0 < cut :=
        lt_trans (Nat.succ_pos q.val) hq
      have hseg_root :
          (S.path.bottomProjectionSegment D hpath.2.2.1 cut hcut).IsRootPath := by
        have hrootlike :
            (S.bottomProjectedStep D
              ⟨hpath, _hafterRank, _hrank, _hroot_step, hnonroot_step, _hunchanged⟩
              cut hcut).IsRootLike :=
          ((S.bottomProjectedStep D
            ⟨hpath, _hafterRank, _hrank, _hroot_step, hnonroot_step, _hunchanged⟩
            cut hcut).not_charged_iff_rootLike).1 hnotCharged
        change (S.path.bottomProjectionSegment D hpath.2.2.1 cut hcut).IsRootPath
          at hrootlike
        exact hrootlike
      let seg := S.path.bottomProjectionSegment D hpath.2.2.1 cut hcut
      have hseg_len_pos : 0 < seg.len := by
        simpa [seg, RawCompressionPath.bottomProjectionSegment,
          RawCompressionPath.bottomProjectionLength] using hcut_pos
      let bi : Fin (S.path.bottomProjectionLength D cut hcut) :=
        seg.lastIndex hseg_len_pos
      let orig : Fin (n + 1) := S.path.bottomProjectionIndex D cut hcut bi
      have horig_last : orig.val + 1 = S.path.len.val := by
        simp [orig, bi, seg, RawCompressionPath.ProjectedPathSegment.lastIndex,
          RawCompressionPath.bottomProjectionIndex,
          RawCompressionPath.bottomProjectionSegment,
          RawCompressionPath.bottomProjectionLength]
        omega
      have horig_target : S.path.node orig = S.path.target :=
        hpath.2.2.2 orig horig_last
      have hroot_eq :
          D.bottomParent (S.path.bottomProjectionNode D cut hcut bi) =
            S.path.bottomProjectionNode D cut hcut bi := by
        simpa [seg] using hseg_root hseg_len_pos
      have hroot_val :
          (D.bottomParent (S.path.bottomProjectionNode D cut hcut bi)).1 =
            (S.path.bottomProjectionNode D cut hcut bi).1 :=
        congrArg Subtype.val hroot_eq
      by_cases hb : D.IsBottom (S.before.parent S.path.target)
      · have hparent_bottom :
            D.IsBottom (S.before.parent (S.path.node orig)) := by
          simpa [horig_target] using hb
        have hbottom_val :
            (D.bottomParent (S.path.bottomProjectionNode D cut hcut bi)).1 =
              S.before.parent (S.path.node orig) :=
          D.bottomParent_val_of_parent_bottom
            (S.path.bottomProjectionNode D cut hcut bi) hparent_bottom
        have hnode_val :
            (S.path.bottomProjectionNode D cut hcut bi).1 = S.path.target := by
          simpa [RawCompressionPath.bottomProjectionNode_val, orig] using horig_target
        have hparent_target :
            S.before.parent S.path.target = S.path.target := by
          rw [hbottom_val, hnode_val] at hroot_val
          simpa [horig_target] using hroot_val
        exact False.elim (hnonroot hparent_target)
      · unfold RawDissection.IsBottom at hb
        exact Decidable.not_not.mp hb
  rw [hrewire]
  exact htarget_parent_top

/--
Source-relevant bottom exceptional cost is exactly the number of bottom-prefix
edges when the source step is nonroot and the bottom projection is root-like,
and zero otherwise.
-/
theorem sourceRelevantBottomExceptionalCost_eq_if_nonroot_not_charged
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.sourceRelevantBottomExceptionalCost D hS cut hcut =
      (by
        classical
        exact if S.path.IsNonrootPath S.before ∧
          Not (S.bottomProjectedStep D hS cut hcut).IsCharged then
          cut - 1
        else
          0) := by
  classical
  let B := S.bottomProjectedStep D hS cut hcut
  have hcost : B.cost = cut - 1 := by
    change (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost = cut - 1
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost
    rw [RawCompressionPath.bottomProjectionSegment_len]
    simp [RawCompressionPath.bottomProjectionLength]
  by_cases hnonroot : S.path.IsNonrootPath S.before
  · by_cases hcharged : B.IsCharged
    · have hnot : Not (S.path.IsNonrootPath S.before ∧ Not B.IsCharged) := by
        intro h
        exact h.2 hcharged
      simp [sourceRelevantBottomExceptionalCost, hnonroot, hcharged, B]
    · have hcond : S.path.IsNonrootPath S.before ∧ Not B.IsCharged :=
        ⟨hnonroot, hcharged⟩
      simp [sourceRelevantBottomExceptionalCost, hnonroot, hcharged, hcost, B]
  · have hcond : Not (S.path.IsNonrootPath S.before ∧ Not B.IsCharged) := by
      intro h
      exact hnonroot h.1
    simp [sourceRelevantBottomExceptionalCost, hnonroot]

/-- Source-relevant bottom exceptional cost is always bounded by source step cost. -/
theorem sourceRelevantBottomExceptionalCost_le_cost
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.sourceRelevantBottomExceptionalCost D hS cut hcut <= S.cost := by
  classical
  by_cases hnonroot : S.path.IsNonrootPath S.before
  · have hrel :
        S.sourceRelevantBottomExceptionalCost D hS cut hcut =
          (S.bottomProjectedStep D hS cut hcut).exceptionalCost := by
      simp [sourceRelevantBottomExceptionalCost, hnonroot]
    have hexception :
        (S.bottomProjectedStep D hS cut hcut).exceptionalCost <=
          (S.bottomProjectedStep D hS cut hcut).cost :=
      (S.bottomProjectedStep D hS cut hcut).exceptionalCost_le_cost
    have hbottom_cost :
        (S.bottomProjectedStep D hS cut hcut).cost <= S.cost := by
      have hnotroot : Not (S.path.IsRootPath S.before) := by
        intro hroot
        exact hnonroot hroot
      unfold RawCompressionStep.bottomProjectedStep
        RawCompressionPath.ProjectedCompressionStep.cost
        RawCompressionPath.ProjectedPathSegment.edgeCost
      unfold RawCompressionPath.bottomProjectionSegment
        RawCompressionPath.bottomProjectionLength
      unfold cost RawCompressionPath.sourceCost RawCompressionPath.cost
      rw [if_neg hnotroot]
      exact Nat.sub_le_sub_right hcut.1 1
    rw [hrel]
    exact hexception.trans hbottom_cost
  · rw [S.sourceRelevantBottomExceptionalCost_eq_zero_of_not_nonroot D hS cut hcut hnonroot]
    exact Nat.zero_le S.cost

/--
Step-level source-relevant accounting.  Bottom projected exceptional cost is
kept only in the source-nonroot case; source-rootpath projected exceptions are
bypassed because the original source cost is zero.
-/
theorem cost_le_sourceRelevantProjectedParts
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).consumableCost +
        S.sourceRelevantBottomExceptionalCost D hS cut hcut +
        (S.topProjectedStep D hS cut hcut).consumableCost +
          (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
  classical
  let B := S.bottomProjectedStep D hS cut hcut
  by_cases hnonroot : S.path.IsNonrootPath S.before
  · have hbase := S.cost_le_bottomCost_add_topConsumable_add_topNonroot D hS cut hcut
    have hsplit : B.cost = B.consumableCost + B.exceptionalCost :=
      B.cost_eq_consumableCost_add_exceptionalCost
    have hrel :
        S.sourceRelevantBottomExceptionalCost D hS cut hcut = B.exceptionalCost := by
      simp [sourceRelevantBottomExceptionalCost, hnonroot, B]
    calc
      S.cost <=
          B.cost +
            (S.topProjectedStep D hS cut hcut).consumableCost +
              (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
          simpa [B] using hbase
      _ = B.consumableCost + B.exceptionalCost +
            (S.topProjectedStep D hS cut hcut).consumableCost +
              (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
          rw [hsplit]
      _ = (S.bottomProjectedStep D hS cut hcut).consumableCost +
            S.sourceRelevantBottomExceptionalCost D hS cut hcut +
            (S.topProjectedStep D hS cut hcut).consumableCost +
              (S.topProjectedStep D hS cut hcut).nonrootIndicator := by
          rw [hrel]
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

/--
Every nonempty rank-valid forest supports a zero-cost no-op source step:
follow a root by a length-two rootpath and leave the forest unchanged.
-/
theorem exists_valid_zero_cost_noop_step
    (F : RawRankedForest n r)
    (hF : F.IsRankValid)
    (hn : 0 < n) :
    Exists fun S : RawCompressionStep n r =>
      S.IsValid /\
        S.before = F /\
          S.after = F /\
            S.cost = 0 := by
  classical
  rcases F.exists_root_of_isRankValid hF hn with ⟨root, hroot⟩
  let P : RawCompressionPath n := {
    len := ⟨2, by omega⟩
    node := fun _ => root
    target := root
  }
  let S : RawCompressionStep n r := {
    before := F
    after := F
    path := P
  }
  refine ⟨S, ?_, rfl, rfl, ?_⟩
  · refine ⟨?hpath, hF, ?hrank, ?hrootStep, ?hnonroot, ?hunchanged⟩
    · refine ⟨hF, ?hlen, ?hchain, ?hlast⟩
      · norm_num [P]
      · intro i j _hij _hj
        simpa [P] using hroot
      · intro i _hi
        rfl
    · intro v
      rfl
    · intro _hrootPath
      rfl
    · intro hnonroot
      exact False.elim (hnonroot hroot)
    · intro v _hv
      rfl
  · simp [S, P, RawCompressionStep.cost, RawCompressionPath.sourceCost,
      RawCompressionPath.IsRootPath, RawRankedForest.IsRoot, hroot]

/-- Cast a raw compression step across a propositional vertex-count equality. -/
noncomputable def castVertexCount
    {n n' r : Nat}
    (S : RawCompressionStep n r)
    (h : n = n') :
    RawCompressionStep n' r := by
  cases h
  exact S

@[simp]
theorem castVertexCount_cost
    {n n' r : Nat}
    (S : RawCompressionStep n r)
    (h : n = n') :
    (S.castVertexCount h).cost = S.cost := by
  cases h
  rfl

theorem castVertexCount_isValid
    {n n' r : Nat}
    (S : RawCompressionStep n r)
    (h : n = n')
    (hS : S.IsValid) :
    (S.castVertexCount h).IsValid := by
  cases h
  exact hS

theorem castVertexCount_before_hasRankThresholdPacking
    {n n' r : Nat}
    (S : RawCompressionStep n r)
    (h : n = n')
    (hpack : S.before.HasRankThresholdPacking) :
    (S.castVertexCount h).before.HasRankThresholdPacking := by
  cases h
  exact hpack

theorem castVertexCount_after_hasRankThresholdPacking
    {n n' r : Nat}
    (S : RawCompressionStep n r)
    (h : n = n')
    (hpack : S.after.HasRankThresholdPacking) :
    (S.castVertexCount h).after.HasRankThresholdPacking := by
  cases h
  exact hpack

/-- A step with positive source cost must be a source nonrootpath. -/
theorem path_isNonrootPath_of_cost_pos
    (S : RawCompressionStep n r)
    (hcost : 0 < S.cost) :
    S.path.IsNonrootPath S.before := by
  classical
  by_contra hnonroot
  have hroot : S.path.IsRootPath S.before := by
    simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
      RawRankedForest.IsRoot] using hnonroot
  have hzero : S.cost = 0 := by
    simp [RawCompressionStep.cost, RawCompressionPath.sourceCost, hroot]
  omega

/-- On a source nonrootpath, step cost is the raw edge count. -/
theorem cost_eq_path_cost_of_nonroot
    (S : RawCompressionStep n r)
    (hnonroot : S.path.IsNonrootPath S.before) :
    S.cost = S.path.cost := by
  classical
  have hnotRoot : Not (S.path.IsRootPath S.before) := by
    simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
      RawRankedForest.IsRoot] using hnonroot
  simp [RawCompressionStep.cost, RawCompressionPath.sourceCost, hnotRoot]

/-- The old parent of a charged edge in a source-nonroot step has positive rank. -/
theorem oldParentRank_pos_of_nonroot_index
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (hnonroot : S.path.IsNonrootPath S.before)
    (q : Fin (n + 1))
    (hq : q.val + 1 < S.path.len.val) :
    0 < S.before.rankNat (S.before.parent (S.path.node q)) := by
  let next : Fin (n + 1) := ⟨q.val + 1, by
    have hlen_le : S.path.len.val <= n + 1 := Nat.le_of_lt_succ S.path.len.isLt
    omega⟩
  have hnext_active : next.val < S.path.len.val := by
    simp [next]
    omega
  have hparent_next :
      S.before.parent (S.path.node q) = S.path.node next := by
    exact hS.1.2.2.1 q next (by simp [next]) hnext_active
  have hq_lt_next : q.val < next.val := by simp [next]
  have hrank_q_lt_next :
      S.before.rankNat (S.path.node q) < S.before.rankNat (S.path.node next) :=
    S.path.rankNat_lt_of_lt_active_of_nonroot hS.1 hnonroot hq_lt_next hnext_active
  rw [hparent_next]
  exact lt_of_le_of_lt (Nat.zero_le _) hrank_q_lt_next

/--
For a charged edge index in a valid source-nonroot step, the rank of the old
parent fits the legacy base-accounting rank coordinate.
-/
theorem oldParentRank_sub_one_lt_of_nonroot_index
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (hnonroot : S.path.IsNonrootPath S.before)
    (q : Fin (n + 1))
    (hq : q.val + 1 < S.path.len.val) :
    S.before.rankNat (S.before.parent (S.path.node q)) - 1 < r - 1 := by
  classical
  let next : Fin (n + 1) := ⟨q.val + 1, by
    have hlen_le : S.path.len.val <= n + 1 := Nat.le_of_lt_succ S.path.len.isLt
    omega⟩
  have hnext_active : next.val < S.path.len.val := by
    simp [next]
    omega
  have hparent_next :
      S.before.parent (S.path.node q) = S.path.node next := by
    exact hS.1.2.2.1 q next (by simp [next]) hnext_active
  have hq_lt_next : q.val < next.val := by simp [next]
  have hrank_q_lt_next :
      S.before.rankNat (S.path.node q) < S.before.rankNat (S.path.node next) :=
    S.path.rankNat_lt_of_lt_active_of_nonroot hS.1 hnonroot hq_lt_next hnext_active
  have hold_pos :
      0 < S.before.rankNat (S.before.parent (S.path.node q)) := by
    exact S.oldParentRank_pos_of_nonroot_index hS hnonroot q hq
  have hlen_one : 1 <= S.path.len.val := by omega
  let last := S.path.lastIndex hlen_one
  have hlast_active : last.val < S.path.len.val :=
    S.path.lastIndex_active hlen_one
  have hnext_le_last : next.val <= last.val := by
    simp [next, last, RawCompressionPath.lastIndex]
    omega
  have hancestor :
      S.before.IsAncestor (S.path.node next) (S.path.node last) :=
    S.path.ancestor_of_le_active hS.1.2.2.1 hnext_le_last hlast_active
  rcases hancestor with ⟨t, ht⟩
  have hrank_next_le_last :
      S.before.rankNat (S.path.node next) <= S.before.rankNat (S.path.node last) := by
    simpa [ht] using S.before.rankNat_le_parentIter hS.1.1 t (S.path.node next)
  have hlast_target : S.path.node last = S.path.target :=
    hS.1.2.2.2 last (S.path.lastIndex_succ hlen_one)
  have hrank_target_lt_parent :
      S.before.rankNat S.path.target < S.before.rankNat (S.before.parent S.path.target) :=
    hS.1.1 S.path.target hnonroot
  have hparent_target_le_r :
      S.before.rankNat (S.before.parent S.path.target) <= r :=
    Nat.le_of_lt_succ ((S.before.rank (S.before.parent S.path.target)).isLt)
  have hold_lt_r :
      S.before.rankNat (S.before.parent (S.path.node q)) < r := by
    rw [hparent_next]
    calc
      S.before.rankNat (S.path.node next)
          <= S.before.rankNat (S.path.node last) := hrank_next_le_last
      _ = S.before.rankNat S.path.target := by rw [hlast_target]
      _ < S.before.rankNat (S.before.parent S.path.target) := hrank_target_lt_parent
      _ <= r := hparent_target_le_r
  omega

/-- A charged edge strictly raises the parent-rank of its lower endpoint. -/
theorem oldParentRank_lt_after_parentRank_of_nonroot_index
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (hnonroot : S.path.IsNonrootPath S.before)
    (q : Fin (n + 1))
    (hq : q.val + 1 < S.path.len.val) :
    S.before.rankNat (S.before.parent (S.path.node q)) <
      S.after.rankNat (S.after.parent (S.path.node q)) := by
  classical
  let next : Fin (n + 1) := ⟨q.val + 1, by
    have hlen_le : S.path.len.val <= n + 1 := Nat.le_of_lt_succ S.path.len.isLt
    omega⟩
  have hnext_active : next.val < S.path.len.val := by
    simp [next]
    omega
  have hparent_next :
      S.before.parent (S.path.node q) = S.path.node next := by
    exact hS.1.2.2.1 q next (by simp [next]) hnext_active
  have hlen_one : 1 <= S.path.len.val := by omega
  let last := S.path.lastIndex hlen_one
  have hlast_active : last.val < S.path.len.val :=
    S.path.lastIndex_active hlen_one
  have hnext_le_last : next.val <= last.val := by
    simp [next, last, RawCompressionPath.lastIndex]
    omega
  have hancestor :
      S.before.IsAncestor (S.path.node next) (S.path.node last) :=
    S.path.ancestor_of_le_active hS.1.2.2.1 hnext_le_last hlast_active
  rcases hancestor with ⟨t, ht⟩
  have hrank_next_le_last :
      S.before.rankNat (S.path.node next) <= S.before.rankNat (S.path.node last) := by
    simpa [ht] using S.before.rankNat_le_parentIter hS.1.1 t (S.path.node next)
  have hlast_target : S.path.node last = S.path.target :=
    hS.1.2.2.2 last (S.path.lastIndex_succ hlen_one)
  have hrank_target_lt_parent :
      S.before.rankNat S.path.target < S.before.rankNat (S.before.parent S.path.target) :=
    hS.1.1 S.path.target hnonroot
  have hold_lt_new :
      S.before.rankNat (S.before.parent (S.path.node q)) <
        S.before.rankNat (S.before.parent S.path.target) := by
    rw [hparent_next]
    exact lt_of_le_of_lt
      (by
        calc
          S.before.rankNat (S.path.node next)
              <= S.before.rankNat (S.path.node last) := hrank_next_le_last
          _ = S.before.rankNat S.path.target := by rw [hlast_target])
      hrank_target_lt_parent
  have hcomp : S.path.IsCompressedVertex (S.path.node q) := by
    exact ⟨q, hq, rfl⟩
  have hafter_parent :
      S.after.parent (S.path.node q) = S.before.parent S.path.target :=
    hS.2.2.2.2.1 hnonroot (S.path.node q) hcomp
  have hrank_pres :
      S.after.rankNat (S.before.parent S.path.target) =
        S.before.rankNat (S.before.parent S.path.target) := by
    unfold RawRankedForest.rankNat
    exact congrArg Fin.val (hS.2.2.1 (S.before.parent S.path.target))
  simpa [hafter_parent, hrank_pres] using hold_lt_new

/-- Parent ranks never decrease across a valid source step. -/
theorem parent_rankNat_le_after_parent_rankNat
    (S : RawCompressionStep n r)
    (hS : S.IsValid)
    (v : Fin n) :
    S.before.rankNat (S.before.parent v) <=
      S.after.rankNat (S.after.parent v) := by
  classical
  by_cases hroot : S.path.IsRootPath S.before
  · have hparent := hS.2.2.2.1 hroot
    have hrank_pres :
        S.after.rankNat (S.before.parent v) =
          S.before.rankNat (S.before.parent v) := by
      unfold RawRankedForest.rankNat
      exact congrArg Fin.val (hS.2.2.1 (S.before.parent v))
    simpa [hparent, hrank_pres]
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v
    · rcases hcomp with ⟨q, hq, hnode⟩
      have hstrict :=
        S.oldParentRank_lt_after_parentRank_of_nonroot_index hS hnonroot q hq
      simpa [hnode] using le_of_lt hstrict
    · have hparent := hS.2.2.2.2.2 v hcomp
      have hrank_pres :
          S.after.rankNat (S.before.parent v) =
            S.before.rankNat (S.before.parent v) := by
        unfold RawRankedForest.rankNat
        exact congrArg Fin.val (hS.2.2.1 (S.before.parent v))
      simpa [hparent, hrank_pres]

end RawCompressionStep

namespace RawCompressionExecution

variable {m n r : Nat}

/-- Legacy base accounting against an external vertex budget. -/
def HasLegacyBaseRankAccountingWithBudget
    (E : RawCompressionExecution m n r)
    (N : Nat) : Prop :=
  Exists fun charge : E.ChargeUnit -> Prod (Fin N) (Fin (r - 1)) =>
    Function.Injective charge

/-- Before/after rank-threshold packing against an external vertex budget. -/
def HasRankThresholdPackingWithBudget
    (E : RawCompressionExecution m n r)
    (N : Nat) : Prop :=
  forall i : Fin m,
    (E.step i).before.HasRankThresholdPackingWithBudget N /\
      (E.step i).after.HasRankThresholdPackingWithBudget N

/-- Faithful base/rank accounting against an external vertex budget. -/
def HasBaseRankAccountingWithBudget
    (E : RawCompressionExecution m n r)
    (N : Nat) : Prop :=
  E.HasLegacyBaseRankAccountingWithBudget N /\
    E.HasRankThresholdPackingWithBudget N

/-- Ordinary faithful base/rank accounting is budgeted accounting at the exact size. -/
theorem hasBaseRankAccountingWithBudget_self
    (E : RawCompressionExecution m n r)
    (h : E.HasBaseRankAccounting) :
    E.HasBaseRankAccountingWithBudget n := by
  refine ⟨h.1, ?_⟩
  intro i
  exact
    ⟨RawRankedForest.hasRankThresholdPackingWithBudget_self
        (E.step i).before (h.2 i).1,
      RawRankedForest.hasRankThresholdPackingWithBudget_self
        (E.step i).after (h.2 i).2⟩

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

/-- Parent ranks do not decrease across adjacent valid execution slots. -/
theorem parent_rankNat_le_before_of_adjacent
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    {i j : Fin m}
    (hij : i.val + 1 = j.val)
    (v : Fin n) :
    (E.step i).before.rankNat ((E.step i).before.parent v) <=
      (E.step j).before.rankNat ((E.step j).before.parent v) := by
  have hlocal :=
    (E.step i).parent_rankNat_le_after_parent_rankNat (hsteps i) v
  have hstate_ij : (E.step i).after = (E.step j).before := hstate i j hij
  simpa [hstate_ij] using hlocal

/-- Parent ranks do not decrease from an earlier before-state to a later one. -/
theorem parent_rankNat_le_before_of_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    {i j : Fin m}
    (hij_le : i.val <= j.val)
    (v : Fin n) :
    (E.step i).before.rankNat ((E.step i).before.parent v) <=
      (E.step j).before.rankNat ((E.step j).before.parent v) := by
  rcases Nat.exists_eq_add_of_le hij_le with ⟨d, hd⟩
  revert i j
  induction d with
  | zero =>
      intro i j hij_le hd
      have hvals : i.val = j.val := by omega
      have hfin : i = j := Fin.ext hvals
      subst j
      exact le_rfl
  | succ d ih =>
      intro i j hij_le hd
      let mid : Fin m := ⟨i.val + d, by omega⟩
      have hi_mid : i.val <= mid.val := by simp [mid]
      have hmid_eq : mid.val = i.val + d := by rfl
      have hmid_j : mid.val + 1 = j.val := by
        simp [mid]
        omega
      have hprev :
          (E.step i).before.rankNat ((E.step i).before.parent v) <=
            (E.step mid).before.rankNat ((E.step mid).before.parent v) :=
        ih hi_mid hmid_eq
      have hnext :
          (E.step mid).before.rankNat ((E.step mid).before.parent v) <=
            (E.step j).before.rankNat ((E.step j).before.parent v) :=
        E.parent_rankNat_le_before_of_adjacent hsteps hstate hmid_j v
      exact hprev.trans hnext

/--
After a valid slot, the same vertex's parent rank is bounded by its parent rank
before any strictly later slot.
-/
theorem parent_rankNat_le_later_before_of_lt
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    {i j : Fin m}
    (hij_lt : i.val < j.val)
    (v : Fin n) :
    (E.step i).after.rankNat ((E.step i).after.parent v) <=
      (E.step j).before.rankNat ((E.step j).before.parent v) := by
  let next : Fin m := ⟨i.val + 1, by omega⟩
  have hi_next : i.val + 1 = next.val := rfl
  have hstate_next : (E.step i).after = (E.step next).before :=
    hstate i next hi_next
  have hnext_le_j : next.val <= j.val := by
    simp [next]
    omega
  have hle :
      (E.step next).before.rankNat ((E.step next).before.parent v) <=
        (E.step j).before.rankNat ((E.step j).before.parent v) :=
    E.parent_rankNat_le_before_of_le hsteps hstate hnext_le_j v
  simpa [hstate_next] using hle

/--
Semantic source executions carry the legacy base-rank accounting injection.

The charge map sends each source-cost unit to its lower endpoint and the
rank of that endpoint's old parent, shifted down by one. Same-slot collisions
are ruled out by strict rank increase along source-nonroot paths; cross-slot
collisions are ruled out because the charged endpoint's parent rank strictly
increases at the earlier slot and never decreases afterward.
-/
theorem hasLegacyBaseRankAccounting_of_semanticallyValid
    (E : RawCompressionExecution m n r)
    (hsem : E.IsSemanticallyValid) :
    E.HasLegacyBaseRankAccounting := by
  classical
  let charge : E.ChargeUnit -> Prod (Fin n) (Fin (r - 1)) := fun u => by
    let S := E.step u.1
    have hcost_pos : 0 < S.cost :=
      lt_of_le_of_lt (Nat.zero_le _) u.2.isLt
    have hnonroot : S.path.IsNonrootPath S.before :=
      S.path_isNonrootPath_of_cost_pos hcost_pos
    have hcost_eq : S.cost = S.path.cost :=
      S.cost_eq_path_cost_of_nonroot hnonroot
    let q : Fin (n + 1) := ⟨u.2.val, by
      have hlen_lt : S.path.len.val < n + 2 := S.path.len.isLt
      have hu : u.2.val < S.cost := u.2.isLt
      unfold RawCompressionPath.cost at hcost_eq
      omega⟩
    have hq : q.val + 1 < S.path.len.val := by
      have hu : u.2.val < S.cost := u.2.isLt
      unfold RawCompressionPath.cost at hcost_eq
      simp [q]
      omega
    exact
      (S.path.node q,
        ⟨S.before.rankNat (S.before.parent (S.path.node q)) - 1,
          S.oldParentRank_sub_one_lt_of_nonroot_index
            (hsem.1 u.1) hnonroot q hq⟩)
  refine ⟨charge, ?_⟩
  intro a b hab
  rcases a with ⟨i, ai⟩
  rcases b with ⟨j, bj⟩
  let Si := E.step i
  let Sj := E.step j
  have hai_pos : 0 < Si.cost :=
    lt_of_le_of_lt (Nat.zero_le _) ai.isLt
  have hbj_pos : 0 < Sj.cost :=
    lt_of_le_of_lt (Nat.zero_le _) bj.isLt
  have hnon_i : Si.path.IsNonrootPath Si.before :=
    Si.path_isNonrootPath_of_cost_pos hai_pos
  have hnon_j : Sj.path.IsNonrootPath Sj.before :=
    Sj.path_isNonrootPath_of_cost_pos hbj_pos
  have hcost_i : Si.cost = Si.path.cost :=
    Si.cost_eq_path_cost_of_nonroot hnon_i
  have hcost_j : Sj.cost = Sj.path.cost :=
    Sj.cost_eq_path_cost_of_nonroot hnon_j
  let qi : Fin (n + 1) := ⟨ai.val, by
    have hlen_lt : Si.path.len.val < n + 2 := Si.path.len.isLt
    have hai : ai.val < Si.cost := ai.isLt
    unfold RawCompressionPath.cost at hcost_i
    omega⟩
  let qj : Fin (n + 1) := ⟨bj.val, by
    have hlen_lt : Sj.path.len.val < n + 2 := Sj.path.len.isLt
    have hbj : bj.val < Sj.cost := bj.isLt
    unfold RawCompressionPath.cost at hcost_j
    omega⟩
  have hqi : qi.val + 1 < Si.path.len.val := by
    have hai : ai.val < Si.cost := ai.isLt
    unfold RawCompressionPath.cost at hcost_i
    simp [qi]
    omega
  have hqj : qj.val + 1 < Sj.path.len.val := by
    have hbj : bj.val < Sj.cost := bj.isLt
    unfold RawCompressionPath.cost at hcost_j
    simp [qj]
    omega
  have hnode :
      Si.path.node qi = Sj.path.node qj := by
    have h := congrArg Prod.fst hab
    simpa [charge, Si, Sj, qi, qj] using h
  have hrank_sub :
      Si.before.rankNat (Si.before.parent (Si.path.node qi)) - 1 =
        Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) - 1 := by
    have h := congrArg (fun p : Prod (Fin n) (Fin (r - 1)) => p.2.val) hab
    simpa [charge, Si, Sj, qi, qj] using h
  rcases lt_trichotomy i.val j.val with hij | hij_eq | hji
  · have hstrict :
        Si.before.rankNat (Si.before.parent (Si.path.node qi)) <
          Si.after.rankNat (Si.after.parent (Si.path.node qi)) :=
      Si.oldParentRank_lt_after_parentRank_of_nonroot_index
        (hsem.1 i) hnon_i qi hqi
    have hmono :
        Si.after.rankNat (Si.after.parent (Si.path.node qi)) <=
          Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) := by
      have hraw :=
        E.parent_rankNat_le_later_before_of_lt hsem.1 hsem.2 hij
          (Si.path.node qi)
      simpa [Si, Sj, hnode] using hraw
    have hlt :
        Si.before.rankNat (Si.before.parent (Si.path.node qi)) <
          Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) :=
      hstrict.trans_le hmono
    have hpos_i :
        0 < Si.before.rankNat (Si.before.parent (Si.path.node qi)) :=
      Si.oldParentRank_pos_of_nonroot_index (hsem.1 i) hnon_i qi hqi
    have hpos_j :
        0 < Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) :=
      Sj.oldParentRank_pos_of_nonroot_index (hsem.1 j) hnon_j qj hqj
    omega
  · have hfin : i = j := Fin.ext hij_eq
    subst j
    rcases lt_trichotomy ai.val bj.val with hab_lt | hab_eq | hba_lt
    · have hq_lt : qi.val < qj.val := by
        simpa [qi, qj] using hab_lt
      have hqj_active : qj.val < Si.path.len.val := by
        have htmp : qj.val < Sj.path.len.val := by omega
        simpa [Si, Sj] using htmp
      have hne :
          Si.path.node qi ≠ Si.path.node qj :=
        Si.path.node_ne_of_lt_active_of_nonroot
          (hsem.1 i).1 hnon_i hq_lt hqj_active
      exact False.elim (hne (by simpa [Sj] using hnode))
    · have hfin_ai : ai = bj := Fin.ext hab_eq
      subst bj
      rfl
    · have hq_lt : qj.val < qi.val := by
        simpa [qi, qj] using hba_lt
      have hqi_active : qi.val < Si.path.len.val := by
        have htmp : qi.val < Si.path.len.val := by omega
        simpa using htmp
      have hne :
          Si.path.node qj ≠ Si.path.node qi :=
        Si.path.node_ne_of_lt_active_of_nonroot
          (hsem.1 i).1 hnon_i hq_lt hqi_active
      exact False.elim (hne (by simpa [Sj] using hnode.symm))
  · have hstrict :
        Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) <
          Sj.after.rankNat (Sj.after.parent (Sj.path.node qj)) :=
      Sj.oldParentRank_lt_after_parentRank_of_nonroot_index
        (hsem.1 j) hnon_j qj hqj
    have hmono :
        Sj.after.rankNat (Sj.after.parent (Sj.path.node qj)) <=
          Si.before.rankNat (Si.before.parent (Si.path.node qi)) := by
      have hraw :=
        E.parent_rankNat_le_later_before_of_lt hsem.1 hsem.2 hji
          (Sj.path.node qj)
      simpa [Si, Sj, hnode] using hraw
    have hlt :
        Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) <
          Si.before.rankNat (Si.before.parent (Si.path.node qi)) :=
      hstrict.trans_le hmono
    have hpos_i :
        0 < Si.before.rankNat (Si.before.parent (Si.path.node qi)) :=
      Si.oldParentRank_pos_of_nonroot_index (hsem.1 i) hnon_i qi hqi
    have hpos_j :
        0 < Sj.before.rankNat (Sj.before.parent (Sj.path.node qj)) :=
      Sj.oldParentRank_pos_of_nonroot_index (hsem.1 j) hnon_j qj hqj
    omega

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

/-- Sum of bottom projected exceptional costs that are relevant to source cost. -/
noncomputable def bottomSourceRelevantExceptionalCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    Nat :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
    (E.step i).sourceRelevantBottomExceptionalCost (D i) (hsteps i) (cut i) (hcut i)

/-- Canonical-cut source-relevant bottom exceptional cost sum. -/
noncomputable def canonicalBottomSourceRelevantExceptionalCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) : Nat :=
  E.bottomSourceRelevantExceptionalCostSum hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

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

/-- Top projected consumable cost is dominated by the source step-cost sum. -/
theorem topProjectedExecution_consumableCost_le_stepCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    (E.topProjectedExecution hsteps D cut hcut).consumableCost <=
      E.stepCostSum := by
  classical
  unfold RawCompressionPath.ProjectedCompressionExecution.consumableCost
    stepCostSum
  exact Finset.sum_le_sum (by
    intro i _hi
    simpa [topProjectedExecution] using
      (E.step i).topProjectedStep_consumableCost_le_cost
        (D i) (hsteps i) (cut i) (hcut i))

/-- Canonical top projected consumable cost is dominated by source execution cost. -/
theorem canonicalTopProjectedExecution_consumableCost_le_cost
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    (E.canonicalTopProjectedExecution hsteps D).consumableCost <=
      E.cost := by
  rw [E.cost_eq_stepCostSum]
  exact E.topProjectedExecution_consumableCost_le_stepCostSum hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/-- If every displayed top side is the same empty side, top consumable cost is zero. -/
theorem topProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i))
    (i0 : Fin m)
    (hstable : forall i : Fin m, (D i).topFinset = (D i0).topFinset)
    (hcard : (D i0).topFinset.card = 0) :
    (E.topProjectedExecution hsteps D cut hcut).consumableCost = 0 := by
  classical
  unfold RawCompressionPath.ProjectedCompressionExecution.consumableCost
  apply Finset.sum_eq_zero
  intro i _hi
  have hcard_i : (D i).topFinset.card = 0 := by
    rw [hstable i, hcard]
  simpa [topProjectedExecution] using
    (E.step i).topProjectedStep_consumableCost_eq_zero_of_topFinset_card_eq_zero
      (D i) (hsteps i) (cut i) (hcut i) hcard_i

/-- Canonical-cut form of top-side empty-cardinality zero consumable cost. -/
theorem canonicalTopProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (i0 : Fin m)
    (hstable : forall i : Fin m, (D i).topFinset = (D i0).topFinset)
    (hcard : (D i0).topFinset.card = 0) :
    (E.canonicalTopProjectedExecution hsteps D).consumableCost = 0 := by
  exact E.topProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
    hsteps D (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)
    i0 hstable hcard

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
For rank-threshold dissections, once the parent of a fixed raw vertex is top at
one slot, it remains top at the next slot.  This is the adjacent-slot form of
the freshness invariant needed for source-relevant boundary charging.
-/
theorem rankThresholdDissectionFamily_parentTop_of_adjacent
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    {i j : Fin m}
    (hij : i.val + 1 = j.val)
    (v : Fin n)
    (hparent :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step i).before.parent v)) :
    (E.rankThresholdDissectionFamily hsteps s j).IsTop
      ((E.step j).before.parent v) := by
  have hafter :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step i).after.parent v) := by
    exact (E.step i).after_parent_top_of_parent_top
      (E.rankThresholdDissectionFamily hsteps s i) (hsteps i) hparent
  have hstate_ij : (E.step i).after = (E.step j).before := hstate i j hij
  have hbefore_j :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step j).before.parent v) := by
    simpa [hstate_ij] using hafter
  exact (E.rankThresholdDissectionFamily_topStable hsteps hstate s i j hij
    ((E.step j).before.parent v)).1 hbefore_j

/--
Forward persistence of parent-top status for the stable rank-threshold family.
This is the slotwise form needed to show that a bottom vertex charged once by a
source-relevant boundary event cannot later contribute as the lower endpoint of
another bottom-bottom edge.
-/
theorem rankThresholdDissectionFamily_parentTop_of_le
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    {i j : Fin m}
    (hij_le : i.val <= j.val)
    (v : Fin n)
    (hparent :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step i).before.parent v)) :
    (E.rankThresholdDissectionFamily hsteps s j).IsTop
      ((E.step j).before.parent v) := by
  rcases Nat.exists_eq_add_of_le hij_le with ⟨d, hd⟩
  revert i j
  induction d with
  | zero =>
      intro i j hij_le hparent hd
      have hvals : i.val = j.val := by omega
      have hfin : i = j := Fin.ext hvals
      subst j
      exact hparent
  | succ d ih =>
      intro i j hij_le hparent hd
      let mid : Fin m := ⟨i.val + d, by omega⟩
      have hi_mid : i.val <= mid.val := by simp [mid]
      have hmid_eq : mid.val = i.val + d := by rfl
      have hmid_j : mid.val + 1 = j.val := by
        simp [mid]
        omega
      have hparent_mid :
          (E.rankThresholdDissectionFamily hsteps s mid).IsTop
            ((E.step mid).before.parent v) := by
        exact ih hi_mid hparent hmid_eq
      exact E.rankThresholdDissectionFamily_parentTop_of_adjacent
        hsteps hstate s hmid_j v hparent_mid

/--
If a step leaves a vertex with a top parent, then every later slot in the
stable rank-threshold family sees that vertex with a top parent before the
slot begins.
-/
theorem rankThresholdDissectionFamily_parentTop_of_after_lt
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    {i j : Fin m}
    (hij_lt : i.val < j.val)
    (v : Fin n)
    (hafter :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step i).after.parent v)) :
    (E.rankThresholdDissectionFamily hsteps s j).IsTop
      ((E.step j).before.parent v) := by
  let next : Fin m := ⟨i.val + 1, by omega⟩
  have hi_next : i.val + 1 = next.val := rfl
  have hstate_next : (E.step i).after = (E.step next).before :=
    hstate i next hi_next
  have hbefore_next_i :
      (E.rankThresholdDissectionFamily hsteps s i).IsTop
        ((E.step next).before.parent v) := by
    simpa [hstate_next] using hafter
  have hbefore_next :
      (E.rankThresholdDissectionFamily hsteps s next).IsTop
        ((E.step next).before.parent v) :=
    (E.rankThresholdDissectionFamily_topStable hsteps hstate s i next hi_next
      ((E.step next).before.parent v)).1 hbefore_next_i
  have hnext_le_j : next.val <= j.val := by
    simp [next]
    omega
  exact E.rankThresholdDissectionFamily_parentTop_of_le
    hsteps hstate s hnext_le_j v hbefore_next

/--
No future bottom-prefix edge can reuse the lower endpoint of an earlier
source-relevant bottom exceptional edge.  The earlier exceptional edge rewires
that vertex to a top parent; parent-top persistence then contradicts the later
edge's bottom-parent requirement.
-/
theorem rankThreshold_sourceRelevantBottomException_future_bottom_edge_ne
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i j : Fin m}
    (hij : i.val < j.val)
    (hnonroot_i : (E.step i).path.IsNonrootPath (E.step i).before)
    (hnotCharged_i :
      Not ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (qi qj : Fin (n + 1))
    (hqi :
      qi.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
    (hqj :
      qj.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) j) :
    (E.step i).path.node qi ≠ (E.step j).path.node qj := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  change Not ((E.step i).bottomProjectedStep (Dfam i) (hE.1 i)
    (cut i) (hcut i)).IsCharged at hnotCharged_i
  change qi.val + 1 < cut i at hqi
  change qj.val + 1 < cut j at hqj
  have hafter_top :
      (Dfam i).IsTop ((E.step i).after.parent ((E.step i).path.node qi)) :=
    (E.step i).sourceRelevantBottomException_after_parent_top_of_index
      (Dfam i) (hE.1 i) (cut i) (hcut i) hnonroot_i hnotCharged_i qi hqi
  have hfuture_top :
      (Dfam j).IsTop
        ((E.step j).before.parent ((E.step i).path.node qi)) :=
    E.rankThresholdDissectionFamily_parentTop_of_after_lt
      hE.1 hE.2.1 s hij ((E.step i).path.node qi) hafter_top
  intro hsame
  have hcutj_le : cut j <= (E.step j).path.len.val := (hcut j).1
  let rj : Fin (n + 1) := ⟨qj.val + 1, by
    have hlen_le : (E.step j).path.len.val <= n + 1 :=
      Nat.le_of_lt_succ (E.step j).path.len.isLt
    omega⟩
  have hrj_active : rj.val < (E.step j).path.len.val := by
    simp [rj]
    omega
  have hrj_cut : rj.val < cut j := by
    simpa [rj] using hqj
  have hparent_eq :
      (E.step j).before.parent ((E.step j).path.node qj) =
        (E.step j).path.node rj := by
    exact (hE.1 j).1.2.2.1 qj rj (by simp [rj]) hrj_active
  have hrj_bottom : (Dfam j).IsBottom ((E.step j).path.node rj) :=
    (hcut j).2.1 rj hrj_active hrj_cut
  have hparent_bottom_j :
      (Dfam j).IsBottom
        ((E.step j).before.parent ((E.step j).path.node qj)) := by
    simpa [hparent_eq] using hrj_bottom
  have hparent_bottom_i :
      (Dfam j).IsBottom
        ((E.step j).before.parent ((E.step i).path.node qi)) := by
    simpa [hsame] using hparent_bottom_j
  exact hparent_bottom_i hfuture_top

/-- Same-step bottom-prefix lower endpoints on a source-nonroot path are distinct. -/
theorem rankThreshold_sourceRelevantBottomException_same_step_bottom_edge_ne
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hnonroot : (E.step i).path.IsNonrootPath (E.step i).before)
    (qi qj : Fin (n + 1))
    (hij : qi.val < qj.val)
    (hqj :
      qj.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i) :
    (E.step i).path.node qi ≠ (E.step i).path.node qj := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  change qj.val + 1 < cut i at hqj
  have hqj_active : qj.val < (E.step i).path.len.val := by
    have hcut_le : cut i <= (E.step i).path.len.val := (hcut i).1
    omega
  exact (E.step i).path.node_ne_of_lt_active_of_nonroot
    (hE.1 i).1 hnonroot hij hqj_active

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
Increasing enumeration of the charged slots of the rank-threshold top
projected execution.
-/
noncomputable def rankThresholdTopChargedSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) →
      Fin m :=
  (E.canonicalTopProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)).chargedSlot

/-- Every rank-threshold top compacted slot is charged. -/
theorem rankThresholdTopChargedSlot_isCharged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    ((E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).step
        (E.rankThresholdTopChargedSlot hE s q)).IsCharged := by
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [rankThresholdTopChargedSlot, Ct] using Ct.chargedSlot_isCharged q

/-- The rank-threshold top compacted-slot enumeration is strictly increasing. -/
theorem rankThresholdTopChargedSlot_strictMono
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    StrictMono (E.rankThresholdTopChargedSlot hE s) := by
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [rankThresholdTopChargedSlot, Ct] using Ct.chargedSlot_strictMono

/--
A charged rank-threshold top projected step has active path length bounded by
the external padded top budget.  This is the size fact needed to realize the
projected segment as a `RawCompressionPath` over `Fin topRestrictedBudget`.
-/
theorem rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.step i).path.topProjectionLength
        (E.rankThresholdDissectionFamily hE.1 s i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i) <=
      RankThresholdDissection.topRestrictedBudget (n := n) s := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  letI : Fintype D.TopNode := Fintype.ofEquiv D.topFinset D.topNodeEquivTopFinset.symm
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hlen_card :
      seg.len <= Fintype.card D.TopNode := by
    exact seg.len_le_card_of_nonroot
      (RankThresholdDissection.topShiftedRank
        (E.step i).before (hE.1 i).1.1 s)
      (fun v hneq =>
        RankThresholdDissection.topParent_shiftedRank_lt_of_not_root
          (E.step i).before (hE.1 i).1.1 s v hneq)
      hseg_nonroot
  have hcard_eq : Fintype.card D.TopNode = D.topFinset.card := by
    exact (Fintype.card_congr D.topNodeEquivTopFinset).trans
      (Fintype.card_coe D.topFinset)
  have hlen_top : seg.len <= D.topFinset.card := by
    simpa [hcard_eq] using hlen_card
  have htop_budget :
      D.topFinset.card <= RankThresholdDissection.topRestrictedBudget (n := n) s := by
    simpa [D, Dfam, rankThresholdDissectionFamily] using
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
  have hlen_budget :
      seg.len <= RankThresholdDissection.topRestrictedBudget (n := n) s :=
    hlen_top.trans htop_budget
  simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment] using
    hlen_budget

/--
A charged rank-threshold bottom projected slot has no top suffix: the bottom
projection is charged only when the dissection cut reaches the full raw path.
-/
theorem rankThresholdBottomProjectedStep_cut_eq_path_len_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i =
      (E.step i).path.len.val := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  have hnot_lt : Not (cut i < (E.step i).path.len.val) := by
    intro hcut_lt
    let B :=
      (E.step i).bottomProjectedStep (Dfam i) (hE.1 i) (cut i) (hcut i)
    have hroot : B.IsRootLike := by
      simpa [B, RawCompressionStep.bottomProjectedStep,
        RawCompressionPath.ProjectedCompressionStep.IsRootLike] using
        (E.step i).path.bottomProjectionSegment_isRootPath_of_top_nonempty
          (Dfam i) (hE.1 i).1.2.2.1 (cut i) (hcut i) hcut_lt
    have hnot : Not B.IsCharged := (B.not_charged_iff_rootLike).2 hroot
    exact hnot (by simpa [B, Dfam, cut] using hcharged)
  have hcut_le : cut i <= (E.step i).path.len.val := (hcut i).1
  have hcut_eq : cut i = (E.step i).path.len.val := by omega
  simpa [Dfam, cut] using hcut_eq

/-- A charged rank-threshold bottom projected step comes from a nonroot source step. -/
theorem rankThresholdBottomProjectedStep_source_nonroot_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.step i).path.IsNonrootPath (E.step i).before := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hlast_ne⟩
  intro hroot
  have hcut_eq : cut i = (E.step i).path.len.val := by
    simpa [Dfam, cut] using
      E.rankThresholdBottomProjectedStep_cut_eq_path_len_of_charged
        hE s i hcharged
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let orig : Fin (n + 1) :=
    (E.step i).path.bottomProjectionIndex D (cut i) (hcut i) last
  have horig_last : orig.val + 1 = (E.step i).path.len.val := by
    have hseg_len : seg.len = cut i := by
      simp [seg, RawCompressionPath.bottomProjectionSegment,
        RawCompressionPath.bottomProjectionLength]
    have hlast_val : last.val = seg.len - 1 := rfl
    simp [orig, RawCompressionPath.bottomProjectionIndex, hlast_val, hseg_len]
    omega
  have htarget : (E.step i).path.node orig = (E.step i).path.target :=
    (hE.1 i).1.2.2.2 orig horig_last
  have hparent_raw :
      (E.step i).before.parent ((E.step i).path.node orig) =
        (E.step i).path.node orig := by
    simpa [htarget] using hroot
  have hparent_bottom :
      D.IsBottom ((E.step i).before.parent ((E.step i).path.node orig)) := by
    simpa [hparent_raw, seg, orig, RawCompressionPath.bottomProjectionSegment,
      RawCompressionPath.bottomProjectionNode] using (seg.node last).2
  have hbottom_eq : D.bottomParent (seg.node last) = seg.node last := by
    apply Subtype.ext
    have hval :=
      D.bottomParent_val_of_parent_bottom (seg.node last) hparent_bottom
    simpa [seg, orig, RawCompressionPath.bottomProjectionSegment,
      RawCompressionPath.bottomProjectionNode, hparent_raw] using hval
  exact hlast_ne hbottom_eq

/--
A charged rank-threshold bottom projected step has active path length bounded
by the exact bottom coordinate set.  This is the bottom analogue of the padded
top size bridge, but no external budget is needed.
-/
theorem rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.step i).path.bottomProjectionLength
        (E.rankThresholdDissectionFamily hE.1 s i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i) <=
      (E.rankThresholdDissectionFamily hE.1 s i).bottomFinset.card := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  letI : Fintype D.BottomNode :=
    Fintype.ofEquiv D.bottomFinset D.bottomNodeEquivBottomFinset.symm
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hlen_card :
      seg.len <= Fintype.card D.BottomNode := by
    exact seg.len_le_card_of_nonroot
      D.bottomRankNat
      (fun v hneq => D.bottomParent_rank_lt_of_not_root (hE.1 i).1.1 v hneq)
      hseg_nonroot
  have hcard_eq : Fintype.card D.BottomNode = D.bottomFinset.card := by
    exact (Fintype.card_congr D.bottomNodeEquivBottomFinset).trans
      (Fintype.card_coe D.bottomFinset)
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    simpa [hcard_eq] using hlen_card
  simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.bottomProjectionSegment] using
    hlen_bottom

/--
The ordinary exact-size bottom path obtained from a charged rank-threshold
bottom projected segment.
-/
noncomputable def rankThresholdBottomProjectedPath
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    RawCompressionPath
      (E.rankThresholdDissectionFamily hE.1 s i).bottomFinset.card := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    have hraw :=
      E.rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
        hE s i hcharged
    simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.bottomProjectionSegment]
      using hraw
  let e := D.bottomNodeEquivFin
  exact seg.toPaddedPath e hlen_bottom hseg_pos

/-- The named exact-size bottom path has exactly the projected bottom edge cost. -/
theorem rankThresholdBottomProjectedPath_cost_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.rankThresholdBottomProjectedPath hE s i hcharged).cost =
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    have hraw :=
      E.rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
        hE s i hcharged
    simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.bottomProjectionSegment]
      using hraw
  let e := D.bottomNodeEquivFin
  calc
    (E.rankThresholdBottomProjectedPath hE s i hcharged).cost =
        (seg.toPaddedPath e hlen_bottom hseg_pos).cost := by
          simp [rankThresholdBottomProjectedPath, Dfam, cut, D, seg, e]
    _ = seg.edgeCost := by
          simp [RawCompressionPath.ProjectedPathSegment.toPaddedPath,
            RawCompressionPath.cost, RawCompressionPath.ProjectedPathSegment.edgeCost]
    _ =
        ((E.step i).bottomProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
          simp [seg, D, Dfam, cut, RawCompressionStep.bottomProjectedStep,
            RawCompressionPath.ProjectedCompressionStep.cost]

/--
For positive projected bottom cost, the named exact-size bottom path is a valid
ordinary path in the bottom-restricted before forest.
-/
theorem rankThresholdBottomProjectedPath_isValidFor_of_pos
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).bottomProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    (E.rankThresholdBottomProjectedPath hE s i hcharged).IsValidFor G := by
  classical
  intro G
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let G0 := RankThresholdDissection.bottomRestrictedForestFin F hF s
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hpos_edge : 0 < seg.edgeCost := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hpos
  have hseg_len_two : 2 <= seg.len := by
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost at hpos_edge
    omega
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    have hraw :=
      E.rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
        hE s i hcharged
    simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.bottomProjectionSegment]
      using hraw
  let e := D.bottomNodeEquivFin
  let P := seg.toPaddedPath e hlen_bottom hseg_pos
  have hP_valid : P.IsValidFor G0 := by
    refine ⟨?hrank, ?hlen, ?hchain, ?hlast⟩
    · simpa [G0, F, hF] using
        RankThresholdDissection.bottomRestrictedForestFin_isRankValid F hF s
    · simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath]
      exact hseg_len_two
    · intro a b hab hb
      have hbseg : b.val < seg.len := by
        simpa [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath] using hb
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      let bb : Fin seg.len := ⟨b.val, hbseg⟩
      have hparent_seg : D.bottomParent (seg.node aa) = seg.node bb := by
        exact seg.parent_chain (by simpa [aa, bb] using hab)
      have hparent_embed :
          G0.parent (e (seg.node aa)) =
            e (D.bottomParent (seg.node aa)) := by
        simpa [G0, F, hF, D, e] using
          RankThresholdDissection.bottomRestrictedForestFin_parent_of_bottomNode
            F hF s (seg.node aa)
      calc
        G0.parent (P.node a)
            = G0.parent (e (seg.node aa)) := by
                simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, aa, haseg]
        _ = e (D.bottomParent (seg.node aa)) := hparent_embed
        _ = e (seg.node bb) := by rw [hparent_seg]
        _ = P.node b := by
                simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, bb, hbseg]
    · intro a ha
      have ha_seg : a.val + 1 = seg.len := by
        simpa [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath] using ha
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      have haa_last : aa = seg.lastIndex hseg_pos := by
        apply Fin.ext
        simp [aa, RawCompressionPath.ProjectedPathSegment.lastIndex]
        omega
      simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, aa, haseg, haa_last]
  simpa [rankThresholdBottomProjectedPath, Dfam, cut, D, seg, G, F, hF,
    G0, e, P] using hP_valid

/--
Positive-cost charged rank-threshold bottom projected steps lift to valid
ordinary source steps over the exact bottom restriction, with path and cost
equalities exposed.
-/
theorem rankThreshold_bottomProjected_charged_positive_step_lifts_to_valid_step_with_path_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).bottomProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let D := E.rankThresholdDissectionFamily hE.1 s i
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    Exists fun S : RawCompressionStep D.bottomFinset.card s =>
      S.IsValid /\
        S.before = G /\
          S.path = E.rankThresholdBottomProjectedPath hE s i hcharged /\
            S.cost =
              ((E.step i).bottomProjectedStep
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  intro D G
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G0 := RankThresholdDissection.bottomRestrictedForestFin F hF s
  let P := E.rankThresholdBottomProjectedPath hE s i hcharged
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hseg_last_ne⟩
  have hP_valid : P.IsValidFor G0 := by
    simpa [P, G0, F, hF, D, G] using
      E.rankThresholdBottomProjectedPath_isValidFor_of_pos hE s i hcharged hpos
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    have hraw :=
      E.rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
        hE s i hcharged
    simpa [seg, D, Dfam, cut, hcut, RawCompressionPath.bottomProjectionSegment]
      using hraw
  let e := D.bottomNodeEquivFin
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let targetNode : Fin D.bottomFinset.card := e (seg.node last)
  have htarget_parent :
      G0.parent targetNode = e (D.bottomParent (seg.node last)) := by
    simpa [G0, F, hF, D, e, targetNode, last] using
      RankThresholdDissection.bottomRestrictedForestFin_parent_of_bottomNode
        F hF s (seg.node last)
  have hP_target : P.target = targetNode := by
    apply Fin.ext
    simp [P, rankThresholdBottomProjectedPath, Dfam, cut, D, seg, e,
      targetNode, last,
      RawCompressionPath.ProjectedPathSegment.toPaddedPath,
      RawCompressionPath.ProjectedPathSegment.lastIndex]
  have htarget_ne : G0.parent P.target ≠ P.target := by
    intro hroot
    have hroot_target : G0.parent targetNode = targetNode := by
      simpa [hP_target] using hroot
    have hembed :
        e (D.bottomParent (seg.node last)) = e (seg.node last) := by
      exact htarget_parent.symm.trans hroot_target
    have hbottom_eq : D.bottomParent (seg.node last) = seg.node last :=
      e.injective hembed
    exact hseg_last_ne hbottom_eq
  have hP_nonroot : P.IsNonrootPath G0 := by
    simpa [RawCompressionPath.IsNonrootPath] using htarget_ne
  rcases RawCompressionPath.exists_valid_step_of_valid_nonroot_path
      G0 P hP_valid hP_nonroot with ⟨S, hbefore, hpath, hSvalid, hScost⟩
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hSvalid
  · simpa [G0, F, hF, G, D] using hbefore
  · exact hpath
  · exact hScost.trans
      (E.rankThresholdBottomProjectedPath_cost_eq hE s i hcharged)
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, G0, F, hF] using
        RankThresholdDissection.bottomRestrictedForestFin_hasRankThresholdPacking
          F hF hpack s
    exact hbeforePack
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, G0, F, hF] using
        RankThresholdDissection.bottomRestrictedForestFin_hasRankThresholdPacking
          F hF hpack s
    exact S.before.hasRankThresholdPacking_of_rankNat_eq S.after
      (fun v => by
        simp [RawRankedForest.rankNat, hSvalid.2.2.1 v])
      hbeforePack

/--
Increasing enumeration of the charged slots of the rank-threshold bottom
projected execution.
-/
noncomputable def rankThresholdBottomChargedSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) →
      Fin m :=
  (E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)).chargedSlot

/-- Every rank-threshold bottom compacted slot is charged. -/
theorem rankThresholdBottomChargedSlot_isCharged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    ((E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).step
        (E.rankThresholdBottomChargedSlot hE s q)).IsCharged := by
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [rankThresholdBottomChargedSlot, Cb] using Cb.chargedSlot_isCharged q

/-- A compacted charged bottom slot has no top suffix in its source step. -/
theorem rankThresholdBottomChargedSlot_cut_eq_path_len
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i =
      (E.step i).path.len.val := by
  intro i
  have hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged := by
    simpa [i, canonicalBottomProjectedExecution, bottomProjectedExecution]
      using E.rankThresholdBottomChargedSlot_isCharged hE s q
  exact E.rankThresholdBottomProjectedStep_cut_eq_path_len_of_charged
    hE s i hcharged

/-- A compacted charged bottom slot comes from a source nonroot step. -/
theorem rankThresholdBottomChargedSlot_source_nonroot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    (E.step i).path.IsNonrootPath (E.step i).before := by
  intro i
  have hcharged :
      ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged := by
    simpa [i, canonicalBottomProjectedExecution, bottomProjectedExecution]
      using E.rankThresholdBottomChargedSlot_isCharged hE s q
  exact E.rankThresholdBottomProjectedStep_source_nonroot_of_charged
    hE s i hcharged

/-- The rank-threshold bottom compacted-slot enumeration is strictly increasing. -/
theorem rankThresholdBottomChargedSlot_strictMono
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    StrictMono (E.rankThresholdBottomChargedSlot hE s) := by
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [rankThresholdBottomChargedSlot, Cb] using Cb.chargedSlot_strictMono

/--
Dependent projected execution consisting only of the charged slots of the
rank-threshold bottom projection.
-/
noncomputable def rankThresholdBottomChargedProjectedExecution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    RawCompressionPath.ProjectedCompressionExecution
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  exact {
    vertex := fun q => (Dfam (E.rankThresholdBottomChargedSlot hE s q)).BottomNode
    step := fun q =>
      (E.step (E.rankThresholdBottomChargedSlot hE s q)).bottomProjectedStep
        (Dfam (E.rankThresholdBottomChargedSlot hE s q))
        (hE.1 (E.rankThresholdBottomChargedSlot hE s q))
        (E.dissectionCut hE.1 Dfam (E.rankThresholdBottomChargedSlot hE s q))
        (E.dissectionCut_spec hE.1 Dfam
          (E.rankThresholdBottomChargedSlot hE s q))
  }

/-- The charged bottom projected execution cost is the original bottom consumable cost. -/
theorem rankThresholdBottomChargedProjectedExecution_cost_eq_consumableCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost =
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let Cb := E.canonicalBottomProjectedExecution hE.1 Dfam
  simpa [rankThresholdBottomChargedProjectedExecution, rankThresholdBottomChargedSlot,
    RawCompressionPath.ProjectedCompressionExecution.chargedSubexecution,
    Cb, Dfam, canonicalBottomProjectedExecution, bottomProjectedExecution]
    using Cb.chargedSubexecution_cost_eq_consumableCost

/--
Positive-cost compacted charged bottom slots lift to valid ordinary source
steps over their exact bottom restriction.
-/
theorem rankThresholdBottomChargedSlot_positive_lifts_to_valid_step_with_path_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hpos :
      0 <
        ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    let D := E.rankThresholdDissectionFamily hE.1 s i
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    Exists fun S : RawCompressionStep D.bottomFinset.card s =>
      S.IsValid /\
        S.before = G /\
          S.path = E.rankThresholdBottomProjectedPath hE s i
            (by
              simpa [i] using E.rankThresholdBottomChargedSlot_isCharged hE s q) /\
            S.cost =
              ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdBottomChargedSlot hE s q
  have hcharged :
      ((E.step i).bottomProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).IsCharged := by
    simpa [Dfam, i] using E.rankThresholdBottomChargedSlot_isCharged hE s q
  have hpos_i :
      0 <
        ((E.step i).bottomProjectedStep
          (Dfam i) (hE.1 i)
          (E.dissectionCut hE.1 Dfam i)
          (E.dissectionCut_spec hE.1 Dfam i)).cost := by
    simpa [rankThresholdBottomChargedProjectedExecution, Dfam, i] using hpos
  simpa [rankThresholdBottomChargedProjectedExecution, Dfam, i] using
    E.rankThreshold_bottomProjected_charged_positive_step_lifts_to_valid_step_with_path_eq
      hE s i hcharged hpos_i

/--
Zero-cost compacted charged bottom slots are represented by ordinary no-op
steps over the exact bottom restriction.  This packages the local zero-cost
case without asserting that arbitrary uncharged bottom slots can be skipped.
-/
theorem rankThresholdBottomChargedSlot_zero_cost_lifts_to_noop_step
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hcost :
      ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost = 0) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    let D := E.rankThresholdDissectionFamily hE.1 s i
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    Exists fun S : RawCompressionStep D.bottomFinset.card s =>
      S.IsValid /\
        S.before = G /\
          S.after = G /\
            S.cost =
              ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdBottomChargedSlot hE s q
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpackF : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G := RankThresholdDissection.bottomRestrictedForestFin F hF s
  have hcharged :
      ((E.step i).bottomProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).IsCharged := by
    simpa [Dfam, i] using E.rankThresholdBottomChargedSlot_isCharged hE s q
  let seg := (E.step i).path.bottomProjectionSegment D (hE.1 i).1.2.2.1
    (E.dissectionCut hE.1 Dfam i)
    (E.dissectionCut_spec hE.1 Dfam i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, i, RawCompressionStep.bottomProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, _hseg_ne⟩
  have hlen_bottom : seg.len <= D.bottomFinset.card := by
    have hraw :=
      E.rankThresholdBottomProjectedStep_bottomProjectionLength_le_bottomFinset_card_of_charged
        hE s i hcharged
    simpa [seg, D, Dfam, RawCompressionPath.bottomProjectionSegment] using hraw
  have hDpos : 0 < D.bottomFinset.card := lt_of_lt_of_le hseg_pos hlen_bottom
  have hG_rank : G.IsRankValid := by
    simpa [G, F, hF] using
      RankThresholdDissection.bottomRestrictedForestFin_isRankValid F hF s
  rcases RawCompressionStep.exists_valid_zero_cost_noop_step G hG_rank hDpos with
    ⟨S, hSvalid, hSbefore, hSafter, hScost⟩
  refine ⟨S, hSvalid, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [G, F, hF, D, Dfam, i] using hSbefore
  · simpa [G, F, hF, D, Dfam, i] using hSafter
  · exact hScost.trans hcost.symm
  · rw [hSbefore]
    simpa [G, F, hF] using
      RankThresholdDissection.bottomRestrictedForestFin_hasRankThresholdPacking
        F hF hpackF s
  · rw [hSafter]
    simpa [G, F, hF] using
      RankThresholdDissection.bottomRestrictedForestFin_hasRankThresholdPacking
        F hF hpackF s

/--
Every compacted charged bottom slot has an ordinary source step over its exact
bottom restriction with matching cost.  Positive-cost slots use the realized
projected path; zero-cost slots use a no-op.
-/
theorem rankThresholdBottomChargedSlot_lifts_to_valid_step
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    let D := E.rankThresholdDissectionFamily hE.1 s i
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    Exists fun S : RawCompressionStep D.bottomFinset.card s =>
      S.IsValid /\
        S.before = G /\
          S.cost =
            ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost /\
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking := by
  classical
  by_cases hpos :
      0 < ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost
  · rcases
      E.rankThresholdBottomChargedSlot_positive_lifts_to_valid_step_with_path_eq
        hE s q hpos with
        ⟨S, hSvalid, hSbefore, _hSpath, hScost, hSpackBefore, hSpackAfter⟩
    exact ⟨S, hSvalid, hSbefore, hScost, hSpackBefore, hSpackAfter⟩
  · have hzero :
        ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost = 0 :=
      Nat.eq_zero_of_not_pos hpos
    rcases E.rankThresholdBottomChargedSlot_zero_cost_lifts_to_noop_step
        hE s q hzero with
      ⟨S, hSvalid, hSbefore, _hSafter, hScost, hSpackBefore, hSpackAfter⟩
    exact ⟨S, hSvalid, hSbefore, hScost, hSpackBefore, hSpackAfter⟩

/-- Chosen ordinary source step for a compacted charged bottom slot. -/
noncomputable def rankThresholdBottomChargedStep
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    RawCompressionStep
      (E.rankThresholdDissectionFamily hE.1 s
        (E.rankThresholdBottomChargedSlot hE s q)).bottomFinset.card
      s :=
  Classical.choose
    (E.rankThresholdBottomChargedSlot_lifts_to_valid_step hE s q)

/-- Specification of the chosen charged bottom source step. -/
theorem rankThresholdBottomChargedStep_spec
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdBottomChargedSlot hE s q
    let G :=
      RankThresholdDissection.bottomRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let S := E.rankThresholdBottomChargedStep hE s q
    S.IsValid /\
      S.before = G /\
        S.cost =
          ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost /\
          S.before.HasRankThresholdPacking /\
            S.after.HasRankThresholdPacking := by
  simpa [rankThresholdBottomChargedStep] using
    Classical.choose_spec
      (E.rankThresholdBottomChargedSlot_lifts_to_valid_step hE s q)

/--
The chosen dependent charged bottom steps have total cost exactly equal to the
bottom projected consumable cost.
-/
theorem rankThresholdBottomChargedStep_cost_sum_eq_consumableCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (Finset.univ : Finset (Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))).sum
      (fun q => (E.rankThresholdBottomChargedStep hE s q).cost) =
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
  classical
  let Cbc := E.rankThresholdBottomChargedProjectedExecution hE s
  calc
    (Finset.univ : Finset (Fin
        ((E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))).sum
        (fun q => (E.rankThresholdBottomChargedStep hE s q).cost)
        =
      (Finset.univ : Finset (Fin
        ((E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))).sum
        (fun q => (Cbc.step q).cost) := by
          apply Finset.sum_congr rfl
          intro q _hq
          exact (E.rankThresholdBottomChargedStep_spec hE s q).2.2.1
    _ = Cbc.cost := by
          rfl
    _ =
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
          simpa [Cbc] using
            E.rankThresholdBottomChargedProjectedExecution_cost_eq_consumableCost hE s

/--
The ordinary padded path obtained from a charged rank-threshold top projected
segment.  This factors out the local path shape used by the positive-cost lift
so downstream state-equality proofs can reason about its compressed vertices.
-/
noncomputable def rankThresholdTopProjectedPaddedPath
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    RawCompressionPath
      (RankThresholdDissection.topRestrictedBudget (n := n) s) := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, rankThresholdDissectionFamily] using
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun v =>
    ⟨(e v).val, (e v).isLt.trans_le hcard_le_budget⟩
  exact seg.toPaddedPath embed hlen_budget hseg_pos

/--
Compressed vertices of the named rank-threshold padded top path are exactly
the embedded projected top vertices strictly before the projected target.
-/
theorem rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (v : Fin (RankThresholdDissection.topRestrictedBudget (n := n) s)) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Dfam := E.rankThresholdDissectionFamily hE.1 s
    let cut := E.dissectionCut hE.1 Dfam
    let hcut := E.dissectionCut_spec hE.1 Dfam
    let D := Dfam i
    let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
      (cut i) (hcut i)
    let hcard_le_budget : D.topFinset.card <= N := by
      simpa [N, D, Dfam, rankThresholdDissectionFamily] using
        RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).before (hE.1 i).1.1
          ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let e := D.topNodeEquivFin
    let embed : D.TopNode -> Fin N := fun w =>
      ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged).IsCompressedVertex v <->
      Exists fun a : Fin seg.len =>
        a.val + 1 < seg.len /\ embed (seg.node a) = v := by
  classical
  intro N Dfam cut hcut D seg hcard_le_budget e embed
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  simpa [rankThresholdTopProjectedPaddedPath, N, Dfam, cut, hcut, D, seg,
    hcard_le_budget, e, embed] using
    (seg.toPaddedPath_isCompressedVertex_iff embed hlen_budget hseg_pos v)

/--
For a genuine top vertex, compressed-vertex status in the named padded top path
is exactly compressed-vertex status in the original raw path.
-/
theorem rankThresholdTopProjectedPaddedPath_isCompressedVertex_embed_iff_raw
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (x : (E.rankThresholdDissectionFamily hE.1 s i).TopNode) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Dfam := E.rankThresholdDissectionFamily hE.1 s
    let D := Dfam i
    let hcard_le_budget : D.topFinset.card <= N := by
      simpa [N, D, Dfam, rankThresholdDissectionFamily] using
        RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).before (hE.1 i).1.1
          ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let e := D.topNodeEquivFin
    let embed : D.TopNode -> Fin N := fun w =>
      ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged).IsCompressedVertex
        (embed x) <->
      (E.step i).path.IsCompressedVertex x.1 := by
  classical
  intro N Dfam D hcard_le_budget e embed
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  constructor
  · intro hcomp
    have hpadded :=
      (E.rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
        hE s i hcharged (embed x)).1 hcomp
    rcases hpadded with ⟨a, ha, haembed⟩
    have hsegx : seg.node a = x := by
      apply e.injective
      apply Fin.ext
      exact congrArg (fun y : Fin N => y.val) haembed
    let q := (E.step i).path.topProjectionIndex D (cut i) (hcut i) a
    refine ⟨q, ?_, ?_⟩
    · have ha' :
          a.val + 1 < (E.step i).path.len.val - cut i := by
        simpa [seg, RawCompressionPath.topProjectionSegment,
          RawCompressionPath.topProjectionLength] using ha
      simp [q, RawCompressionPath.topProjectionIndex]
      have hcut_le := (hcut i).1
      omega
    · simpa [q, seg, RawCompressionPath.topProjectionSegment,
        RawCompressionPath.topProjectionNode] using congrArg Subtype.val hsegx
  · intro hraw
    rcases hraw with ⟨q, hq, hqnode⟩
    have hq_active : q.val < (E.step i).path.len.val := by omega
    have hcut_le_q : cut i <= q.val := by
      by_contra hnot
      have hq_lt_cut : q.val < cut i := Nat.lt_of_not_ge hnot
      have hbottom : D.IsBottom ((E.step i).path.node q) :=
        (hcut i).2.1 q hq_active hq_lt_cut
      rw [hqnode] at hbottom
      exact hbottom x.2
    have ha_lt :
        q.val - cut i <
          (E.step i).path.topProjectionLength D (cut i) (hcut i) := by
      simp [RawCompressionPath.topProjectionLength]
      omega
    let a :
        Fin ((E.step i).path.topProjectionLength D (cut i) (hcut i)) :=
      ⟨q.val - cut i, ha_lt⟩
    have ha :
        a.val + 1 <
          (E.step i).path.topProjectionLength D (cut i) (hcut i) := by
      simp [a, RawCompressionPath.topProjectionLength]
      omega
    have hidx :
        (E.step i).path.topProjectionIndex D (cut i) (hcut i) a = q := by
      apply Fin.ext
      simp [a, RawCompressionPath.topProjectionIndex]
      omega
    have hsegx : seg.node a = x := by
      apply Subtype.ext
      simpa [seg, RawCompressionPath.topProjectionSegment,
        RawCompressionPath.topProjectionNode, hidx] using hqnode
    have hpadded :=
      (E.rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
        hE s i hcharged (embed x)).2
        ⟨a, by simpa [seg, RawCompressionPath.topProjectionSegment] using ha,
          by simpa using congrArg embed hsegx⟩
    simpa using hpadded

/-- A charged rank-threshold top projected step comes from a nonroot source step. -/
theorem rankThresholdTopProjectedStep_source_nonroot_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.step i).path.IsNonrootPath (E.step i).before := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hlast_ne⟩
  intro hroot
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let orig : Fin (n + 1) :=
    (E.step i).path.topProjectionIndex D (cut i) (hcut i) last
  have horig_last : orig.val + 1 = (E.step i).path.len.val := by
    have hseg_len :
        seg.len = (E.step i).path.len.val - cut i := by
      simp [seg, RawCompressionPath.topProjectionSegment,
        RawCompressionPath.topProjectionLength]
    have hlast_val : last.val = seg.len - 1 := rfl
    simp [orig, RawCompressionPath.topProjectionIndex, hlast_val, hseg_len]
    have hcut_le := (hcut i).1
    omega
  have htarget : (E.step i).path.node orig = (E.step i).path.target :=
    (hE.1 i).1.2.2.2 orig horig_last
  have hparent_raw :
      (E.step i).before.parent ((E.step i).path.node orig) =
        (E.step i).path.node orig := by
    simpa [htarget] using hroot
  have htop_eq : D.topParent (seg.node last) = seg.node last := by
    apply Subtype.ext
    simpa [seg, orig, RawCompressionPath.topProjectionSegment,
      RawCompressionPath.topProjectionNode, RawDissection.topParent] using
      hparent_raw
  exact hlast_ne htop_eq

/-- The named padded top path has exactly the projected top edge cost. -/
theorem rankThresholdTopProjectedPaddedPath_cost_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged).cost =
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, rankThresholdDissectionFamily] using
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun w =>
    ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
  calc
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged).cost =
        (seg.toPaddedPath embed hlen_budget hseg_pos).cost := by
          simp [rankThresholdTopProjectedPaddedPath, N, Dfam, cut, D, seg, e, embed]
    _ = seg.edgeCost := by
          simp [RawCompressionPath.ProjectedPathSegment.toPaddedPath,
            RawCompressionPath.cost, RawCompressionPath.ProjectedPathSegment.edgeCost]
    _ =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
          simp [seg, D, Dfam, cut, RawCompressionStep.topProjectedStep,
            RawCompressionPath.ProjectedCompressionStep.cost]

/--
For positive projected top cost, the named padded top path is a valid ordinary
path in the padded top-restricted before forest.
-/
theorem rankThresholdTopProjectedPaddedPath_isValidFor_of_pos
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    (E.rankThresholdTopProjectedPaddedPath hE s i hcharged).IsValidFor
      (G.padRight hN) := by
  classical
  intro G hN
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G0 := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN0 := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpack s
  let Gpad := G0.padRight hN0
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  have hseg_pos : 0 < seg.len := Classical.choose hseg_nonroot
  have hpos_edge : 0 < seg.edgeCost := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hpos
  have hseg_len_two : 2 <= seg.len := by
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost at hpos_edge
    omega
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpack, G0] using hN0
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun w =>
    ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
  let P := seg.toPaddedPath embed hlen_budget hseg_pos
  have hP_valid : P.IsValidFor Gpad := by
    refine ⟨?hrank, ?hlen, ?hchain, ?hlast⟩
    · simpa [Gpad, G0, hN0, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
          F hF hpack s
    · simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath]
      exact hseg_len_two
    · intro a b hab hb
      have hbseg : b.val < seg.len := by
        simpa [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath] using hb
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      let bb : Fin seg.len := ⟨b.val, hbseg⟩
      have hparent_seg : D.topParent (seg.node aa) = seg.node bb := by
        exact seg.parent_chain (by simpa [aa, bb] using hab)
      have hparent_embed :
          Gpad.parent (embed (seg.node aa)) =
            embed (D.topParent (seg.node aa)) := by
        simpa [Gpad, G0, hN0, F, hF, hpack, D, e, embed] using
          RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
            F hF hpack s (seg.node aa)
      calc
        Gpad.parent (P.node a)
            = Gpad.parent (embed (seg.node aa)) := by
                simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, aa, haseg]
        _ = embed (D.topParent (seg.node aa)) := hparent_embed
        _ = embed (seg.node bb) := by rw [hparent_seg]
        _ = P.node b := by
                simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, bb, hbseg]
    · intro a ha
      have ha_seg : a.val + 1 = seg.len := by
        simpa [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath] using ha
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      have haa_last : aa = seg.lastIndex hseg_pos := by
        apply Fin.ext
        simp [aa, RawCompressionPath.ProjectedPathSegment.lastIndex]
        omega
      simp [P, RawCompressionPath.ProjectedPathSegment.toPaddedPath, aa, haseg, haa_last]
  simpa [rankThresholdTopProjectedPaddedPath, N, Dfam, cut, D, seg, G, hN,
    F, hF, hpack, G0, hN0, Gpad, hcard_le_budget, e, embed, P] using hP_valid

/--
Positive-cost charged rank-threshold top projected steps lift to valid ordinary
padded steps whose path is the named padded top path.
-/
theorem rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step_with_path_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = G.padRight hN /\
          S.path = E.rankThresholdTopProjectedPaddedPath hE s i hcharged /\
            S.cost =
              ((E.step i).topProjectedStep
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  intro N G hN
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G0 := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN0 := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpack s
  let Gpad := G0.padRight hN0
  let P := E.rankThresholdTopProjectedPaddedPath hE s i hcharged
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hseg_last_ne⟩
  have hP_valid : P.IsValidFor Gpad := by
    simpa [P, Gpad, G0, hN0, F, hF, hpack, N, G, hN] using
      E.rankThresholdTopProjectedPaddedPath_isValidFor_of_pos hE s i hcharged hpos
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpack, G0] using hN0
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun w =>
    ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let targetNode : Fin N := embed (seg.node last)
  have htarget_parent :
      Gpad.parent targetNode = embed (D.topParent (seg.node last)) := by
    simpa [Gpad, G0, hN0, F, hF, hpack, D, e, embed, targetNode, last] using
      RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
        F hF hpack s (seg.node last)
  have hP_target : P.target = targetNode := by
    apply Fin.ext
    simp [P, rankThresholdTopProjectedPaddedPath, Dfam, cut, D, seg,
      e, embed, targetNode, last,
      RawCompressionPath.ProjectedPathSegment.toPaddedPath,
      RawCompressionPath.ProjectedPathSegment.lastIndex]
  have htarget_ne : Gpad.parent P.target ≠ P.target := by
    intro hroot
    have hroot_target : Gpad.parent targetNode = targetNode := by
      simpa [hP_target] using hroot
    have hembed :
        embed (D.topParent (seg.node last)) = embed (seg.node last) := by
      exact htarget_parent.symm.trans hroot_target
    have htop_eq : D.topParent (seg.node last) = seg.node last := by
      apply e.injective
      apply Fin.ext
      change (e (D.topParent (seg.node last))).val = (e (seg.node last)).val
      exact congrArg (fun x : Fin N => x.val) hembed
    exact hseg_last_ne htop_eq
  have hP_nonroot : P.IsNonrootPath Gpad := by
    simpa [RawCompressionPath.IsNonrootPath] using htarget_ne
  rcases RawCompressionPath.exists_valid_step_of_valid_nonroot_path
      Gpad P hP_valid hP_nonroot with ⟨S, hbefore, hpath, hSvalid, hScost⟩
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hSvalid
  · simpa [Gpad, G0, hN0, F, hF, hpack, G, hN] using hbefore
  · exact hpath
  · exact hScost.trans
      (E.rankThresholdTopProjectedPaddedPath_cost_eq hE s i hcharged)
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, Gpad, G0, hN0, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
          F hF hpack s
    exact hbeforePack
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, Gpad, G0, hN0, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
          F hF hpack s
    exact S.before.hasRankThresholdPacking_of_rankNat_eq S.after
      (fun v => by
        simp [RawRankedForest.rankNat, hSvalid.2.2.1 v])
      hbeforePack

/--
Positive-cost charged rank-threshold top projected steps lift to valid ordinary
padded steps with exact before, after, and path equalities.
-/
theorem rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step_with_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = Gbefore.padRight hNbefore /\
          S.after = Gafter.padRight hNafter /\
            S.path = E.rankThresholdTopProjectedPaddedPath hE s i hcharged /\
              S.cost =
                ((E.step i).topProjectedStep
                  (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                  (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                  (E.dissectionCut_spec hE.1
                    (E.rankThresholdDissectionFamily hE.1 s) i)).cost /\
                S.before.HasRankThresholdPacking /\
                  S.after.HasRankThresholdPacking := by
  classical
  intro N Gbefore hNbefore Gafter hNafter
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let A := (E.step i).after
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hA : A.IsRankValid := (hE.1 i).2.1
  let hpackF : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let hpackA : A.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).2
  let G0 := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN0 := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpackF s
  let A0 := RankThresholdDissection.topRestrictedForestFin A hA s
  let hNA0 := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    A hA hpackA s
  let Gpad := G0.padRight hN0
  let Apad := A0.padRight hNA0
  let P := E.rankThresholdTopProjectedPaddedPath hE s i hcharged
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hseg_last_ne⟩
  have hP_valid : P.IsValidFor Gpad := by
    simpa [P, Gpad, G0, hN0, F, hF, hpackF, N, Gbefore, hNbefore] using
      E.rankThresholdTopProjectedPaddedPath_isValidFor_of_pos hE s i hcharged hpos
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpackF, G0] using hN0
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun w =>
    ⟨(e w).val, (e w).isLt.trans_le hcard_le_budget⟩
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let targetNode : Fin N := embed (seg.node last)
  have htarget_parent :
      Gpad.parent targetNode = embed (D.topParent (seg.node last)) := by
    simpa [Gpad, G0, hN0, F, hF, hpackF, D, e, embed, targetNode, last] using
      RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
        F hF hpackF s (seg.node last)
  have hP_target : P.target = targetNode := by
    apply Fin.ext
    simp [P, rankThresholdTopProjectedPaddedPath, Dfam, cut, D, seg,
      e, embed, targetNode, last,
      RawCompressionPath.ProjectedPathSegment.toPaddedPath,
      RawCompressionPath.ProjectedPathSegment.lastIndex]
  have htarget_ne : Gpad.parent P.target ≠ P.target := by
    intro hroot
    have hroot_target : Gpad.parent targetNode = targetNode := by
      simpa [hP_target] using hroot
    have hembed :
        embed (D.topParent (seg.node last)) = embed (seg.node last) := by
      exact htarget_parent.symm.trans hroot_target
    have htop_eq : D.topParent (seg.node last) = seg.node last := by
      apply e.injective
      apply Fin.ext
      change (e (D.topParent (seg.node last))).val = (e (seg.node last)).val
      exact congrArg (fun x : Fin N => x.val) hembed
    exact hseg_last_ne htop_eq
  have hP_nonroot : P.IsNonrootPath Gpad := by
    simpa [RawCompressionPath.IsNonrootPath] using htarget_ne
  have hsource_nonroot : (E.step i).path.IsNonrootPath F := by
    simpa [F] using
      E.rankThresholdTopProjectedStep_source_nonroot_of_charged hE s i hcharged
  have hrank :
      forall v : Fin n, A.rankNat v = F.rankNat v := by
    intro v
    unfold A F RawRankedForest.rankNat
    exact congrArg Fin.val ((hE.1 i).2.2.1 v)
  have hcard_eq :
      (RankThresholdDissection.dissection F hF s).topFinset.card =
        (RankThresholdDissection.dissection A hA s).topFinset.card := by
    have hset :
        (RankThresholdDissection.dissection F hF s).topFinset =
          (RankThresholdDissection.dissection A hA s).topFinset := by
      ext v
      simp [RankThresholdDissection.dissection_isTop, hrank v]
    exact congrArg Finset.card hset
  have hraw_target :
      (E.step i).path.target = (seg.node last).1 := by
    let orig : Fin (n + 1) :=
      (E.step i).path.topProjectionIndex D (cut i) (hcut i) last
    have horig_last : orig.val + 1 = (E.step i).path.len.val := by
      have hseg_len :
          seg.len = (E.step i).path.len.val - cut i := by
        simp [seg, RawCompressionPath.topProjectionSegment,
          RawCompressionPath.topProjectionLength]
      have hlast_val : last.val = seg.len - 1 := rfl
      simp [orig, RawCompressionPath.topProjectionIndex, hlast_val, hseg_len]
      have hcut_le := (hcut i).1
      omega
    have hnode_target : (E.step i).path.node orig = (E.step i).path.target :=
      (hE.1 i).1.2.2.2 orig horig_last
    simpa [seg, orig, RawCompressionPath.topProjectionSegment,
      RawCompressionPath.topProjectionNode] using hnode_target.symm
  let S : RawCompressionStep N (r - s - 1) := {
    before := Gpad
    after := Apad
    path := P
  }
  have hSvalid : S.IsValid := by
    refine ⟨hP_valid, ?hrankValid, ?hrankPres, ?hroot, ?hnonroot, ?hunchanged⟩
    · simpa [Apad, A0, hNA0, A, hA, hpackA] using
        RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
          A hA hpackA s
    · intro v
      simpa [S, Gpad, G0, hN0, Apad, A0, hNA0, F, hF, hpackF, A, hA, hpackA] using
        RankThresholdDissection.topRestrictedForestFin_padded_rank_eq_of_rankNat_eq
          F A hF hA hpackF hpackA s hrank v
    · intro hroot
      exact False.elim (hP_nonroot hroot)
    · intro _hnonroot v hcomp
      by_cases hv : v.val < D.topFinset.card
      · let a : Fin D.topFinset.card := ⟨v.val, hv⟩
        let x : D.TopNode := e.symm a
        have hv_embed : v = embed x := by
          apply Fin.ext
          simp [embed, x, a, e]
        have hrawcomp : (E.step i).path.IsCompressedVertex x.1 := by
          have hiff :=
            E.rankThresholdTopProjectedPaddedPath_isCompressedVertex_embed_iff_raw
              hE s i hcharged x
          exact hiff.1 (by simpa [P, hv_embed] using hcomp)
        have hafter_raw : A.parent x.1 = F.parent (E.step i).path.target := by
          simpa [A, F] using
            (hE.1 i).2.2.2.2.1 hsource_nonroot x.1 hrawcomp
        have hparent_to_target :
            A.parent x.1 = (D.topParent (seg.node last)).1 := by
          rw [hafter_raw, hraw_target]
          rfl
        have hApad :
            Apad.parent v = embed (D.topParent (seg.node last)) := by
          calc
            Apad.parent v = Apad.parent (embed x) := by rw [hv_embed]
            _ = embed (D.topParent (seg.node last)) := by
                simpa [Apad, A0, hNA0, Gpad, G0, hN0, F, hF, hpackF,
                  A, hA, hpackA, D, e, embed] using
                  RankThresholdDissection.topRestrictedForestFin_padded_parent_eq_of_rankNat_eq_of_parent_eq
                      F A hF hA hpackF hpackA s hrank x
                      (D.topParent (seg.node last)) hparent_to_target
        calc
          Apad.parent v = embed (D.topParent (seg.node last)) := hApad
          _ = Gpad.parent targetNode := htarget_parent.symm
          _ = Gpad.parent P.target := by rw [hP_target]
      · exfalso
        have hnot : ¬ P.IsCompressedVertex v := by
          intro hp
          have hpadded :=
            (E.rankThresholdTopProjectedPaddedPath_isCompressedVertex_iff
              hE s i hcharged v).1 hp
          rcases hpadded with ⟨a, _ha, haembed⟩
          have hvlt : v.val < D.topFinset.card := by
            rw [← congrArg (fun z : Fin N => z.val) haembed]
            exact (e (seg.node a)).isLt
          exact hv hvlt
        exact hnot hcomp
    · intro v hnotcomp
      by_cases hv : v.val < D.topFinset.card
      · let a : Fin D.topFinset.card := ⟨v.val, hv⟩
        let x : D.TopNode := e.symm a
        have hv_embed : v = embed x := by
          apply Fin.ext
          simp [embed, x, a, e]
        have hrawnot : ¬ (E.step i).path.IsCompressedVertex x.1 := by
          intro hrawcomp
          apply hnotcomp
          have hiff :=
            E.rankThresholdTopProjectedPaddedPath_isCompressedVertex_embed_iff_raw
              hE s i hcharged x
          exact by simpa [P, hv_embed] using hiff.2 hrawcomp
        have hafter_raw : A.parent x.1 = F.parent x.1 := by
          simpa [A, F] using (hE.1 i).2.2.2.2.2 x.1 hrawnot
        have hparent_to_before :
            A.parent x.1 = (D.topParent x).1 := by
          rw [hafter_raw]
          rfl
        have hApad :
            Apad.parent v = embed (D.topParent x) := by
          calc
            Apad.parent v = Apad.parent (embed x) := by rw [hv_embed]
            _ = embed (D.topParent x) := by
                simpa [Apad, A0, hNA0, Gpad, G0, hN0, F, hF, hpackF,
                  A, hA, hpackA, D, e, embed] using
                  RankThresholdDissection.topRestrictedForestFin_padded_parent_eq_of_rankNat_eq_of_parent_eq
                      F A hF hA hpackF hpackA s hrank x
                      (D.topParent x) hparent_to_before
        have hGpad :
            Gpad.parent v = embed (D.topParent x) := by
          calc
            Gpad.parent v = Gpad.parent (embed x) := by rw [hv_embed]
            _ = embed (D.topParent x) := by
                simpa [Gpad, G0, hN0, F, hF, hpackF, D, e, embed] using
                  RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
                    F hF hpackF s x
        exact hApad.trans hGpad.symm
      · have hvF0 :
            ¬ v.val <
              (RankThresholdDissection.dissection F hF s).topFinset.card := by
          simpa [D, Dfam, F, hF] using hv
        have hvA : ¬ v.val <
            (RankThresholdDissection.dissection A hA s).topFinset.card := by
          omega
        simp [S, Apad, A0, Gpad, G0, A, F, RawRankedForest.padRight, hvF0, hvA]
  have hScost :
      S.cost =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
    have hsource : S.cost = P.cost := by
      unfold S RawCompressionStep.cost RawCompressionPath.sourceCost
      rw [if_neg]
      exact hP_nonroot
    exact hsource.trans
      (E.rankThresholdTopProjectedPaddedPath_cost_eq hE s i hcharged)
  refine ⟨S, hSvalid, ?_, ?_, ?_, hScost, ?_, ?_⟩
  · simp [S, Gpad, G0, F, Gbefore]
  · simp [S, Apad, A0, A, Gafter]
  · rfl
  · simpa [S, Gpad, G0, hN0, F, hF, hpackF] using
      RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
        F hF hpackF s
  · simpa [S, Apad, A0, hNA0, A, hA, hpackA] using
      RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
        A hA hpackA s

/--
Cost-only lift of a charged rank-threshold top projected path into the padded
top budget.  The lifted path is not yet claimed to be valid for the padded
top forest; it only packages the active projected segment into the ordinary
`RawCompressionPath` shape with matching edge cost.
-/
theorem rankThreshold_topProjected_charged_path_lifts_to_padded_path
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    Exists fun P :
      RawCompressionPath
        (RankThresholdDissection.topRestrictedBudget (n := n) s) =>
      P.cost =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hpos, _hne⟩
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, rankThresholdDissectionFamily] using
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun v =>
    ⟨(e v).val, (e v).isLt.trans_le hcard_le_budget⟩
  let defaultNode : Fin N := embed (seg.node ⟨0, hpos⟩)
  let P : RawCompressionPath N := {
    len := ⟨seg.len, by omega⟩
    node := fun j =>
      if hj : j.val < seg.len then embed (seg.node ⟨j.val, hj⟩)
      else defaultNode
    target := embed (seg.node (seg.lastIndex hpos))
  }
  refine ⟨P, ?_⟩
  simp [P, seg, D, Dfam, cut, RawCompressionPath.cost,
    RawCompressionStep.topProjectedStep,
    RawCompressionPath.ProjectedCompressionStep.cost,
    RawCompressionPath.ProjectedPathSegment.edgeCost]

/--
A charged rank-threshold top projected path with positive edge cost lifts
directly to a valid ordinary compression path over the padded top budget, with
the exact same edge cost.  The zero-cost charged case is deliberately excluded:
there the projected path has one top vertex, so ordinary step realization needs
separate identity/no-op handling rather than appending a parent and changing
the projected target.
-/
theorem rankThreshold_topProjected_charged_positive_path_lifts_to_padded_valid_path
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    Exists fun P : RawCompressionPath N =>
      P.IsValidFor (G.padRight hN) /\
        P.cost =
          ((E.step i).topProjectedStep
            (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
            (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpack s
  let Gpad := G.padRight hN
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, _hlast_ne⟩
  have hpos_edge : 0 < seg.edgeCost := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hpos
  have hseg_len_two : 2 <= seg.len := by
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost at hpos_edge
    omega
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpack, G] using hN
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun v =>
    ⟨(e v).val, (e v).isLt.trans_le hcard_le_budget⟩
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let targetNode : Fin N := embed (seg.node last)
  let P : RawCompressionPath N := {
    len := ⟨seg.len, by omega⟩
    node := fun j =>
      if hj : j.val < seg.len then embed (seg.node ⟨j.val, hj⟩)
      else targetNode
    target := targetNode
  }
  refine ⟨P, ?_, ?_⟩
  · refine ⟨?hrank, ?hlen, ?hchain, ?hlast⟩
    · simpa [Gpad, G, hN, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
          F hF hpack s
    · simp [P]
      exact hseg_len_two
    · intro a b hab hb
      have hbseg : b.val < seg.len := by simpa [P] using hb
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      let bb : Fin seg.len := ⟨b.val, hbseg⟩
      have hparent_seg : D.topParent (seg.node aa) = seg.node bb := by
        exact seg.parent_chain (by simpa [aa, bb] using hab)
      have hparent_embed :
          Gpad.parent (embed (seg.node aa)) =
            embed (D.topParent (seg.node aa)) := by
        simpa [Gpad, G, hN, F, hF, hpack, D, e, embed] using
          RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
            F hF hpack s (seg.node aa)
      calc
        Gpad.parent (P.node a)
            = Gpad.parent (embed (seg.node aa)) := by
                simp [P, aa, haseg]
        _ = embed (D.topParent (seg.node aa)) := hparent_embed
        _ = embed (seg.node bb) := by rw [hparent_seg]
        _ = P.node b := by
                simp [P, bb, hbseg]
    · intro a ha
      have ha_seg : a.val + 1 = seg.len := by
        simpa [P] using ha
      have haseg : a.val < seg.len := by
        omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      have haa_last : aa = last := by
        apply Fin.ext
        simp [aa, last, RawCompressionPath.ProjectedPathSegment.lastIndex]
        omega
      simp [P, aa, haseg, targetNode, haa_last]
  · calc
      P.cost = seg.edgeCost := by
          simp [P, RawCompressionPath.cost,
            RawCompressionPath.ProjectedPathSegment.edgeCost]
      _ =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
          simp [seg, D, Dfam, cut, RawCompressionStep.topProjectedStep,
            RawCompressionPath.ProjectedCompressionStep.cost]

/--
Positive-cost charged rank-threshold top projected steps realize as valid
ordinary compression steps over the padded top budget.  The constructed step
uses the exact lifted projected path, so its source cost matches the projected
top cost.
-/
theorem rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged)
    (hpos :
      0 <
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = G.padRight hN /\
          S.cost =
            ((E.step i).topProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).cost /\
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpack s
  let Gpad := G.padRight hN
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, hseg_last_ne⟩
  have hpos_edge : 0 < seg.edgeCost := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.cost] using hpos
  have hseg_len_two : 2 <= seg.len := by
    unfold RawCompressionPath.ProjectedPathSegment.edgeCost at hpos_edge
    omega
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpack, G] using hN
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun v =>
    ⟨(e v).val, (e v).isLt.trans_le hcard_le_budget⟩
  let last : Fin seg.len := seg.lastIndex hseg_pos
  let targetNode : Fin N := embed (seg.node last)
  let P : RawCompressionPath N := {
    len := ⟨seg.len, by omega⟩
    node := fun j =>
      if hj : j.val < seg.len then embed (seg.node ⟨j.val, hj⟩)
      else targetNode
    target := targetNode
  }
  have hP_valid : P.IsValidFor Gpad := by
    refine ⟨?hrank, ?hlen, ?hchain, ?hlast⟩
    · simpa [Gpad, G, hN, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
          F hF hpack s
    · simp [P]
      exact hseg_len_two
    · intro a b hab hb
      have hbseg : b.val < seg.len := by simpa [P] using hb
      have haseg : a.val < seg.len := by omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      let bb : Fin seg.len := ⟨b.val, hbseg⟩
      have hparent_seg : D.topParent (seg.node aa) = seg.node bb := by
        exact seg.parent_chain (by simpa [aa, bb] using hab)
      have hparent_embed :
          Gpad.parent (embed (seg.node aa)) =
            embed (D.topParent (seg.node aa)) := by
        simpa [Gpad, G, hN, F, hF, hpack, D, e, embed] using
          RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
            F hF hpack s (seg.node aa)
      calc
        Gpad.parent (P.node a)
            = Gpad.parent (embed (seg.node aa)) := by
                simp [P, aa, haseg]
        _ = embed (D.topParent (seg.node aa)) := hparent_embed
        _ = embed (seg.node bb) := by rw [hparent_seg]
        _ = P.node b := by
                simp [P, bb, hbseg]
    · intro a ha
      have ha_seg : a.val + 1 = seg.len := by
        simpa [P] using ha
      have haseg : a.val < seg.len := by
        omega
      let aa : Fin seg.len := ⟨a.val, haseg⟩
      have haa_last : aa = last := by
        apply Fin.ext
        simp [aa, last, RawCompressionPath.ProjectedPathSegment.lastIndex]
        omega
      simp [P, aa, haseg, targetNode, haa_last]
  have hP_cost :
      P.cost =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
    calc
      P.cost = seg.edgeCost := by
          simp [P, RawCompressionPath.cost,
            RawCompressionPath.ProjectedPathSegment.edgeCost]
      _ =
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost := by
          simp [seg, D, Dfam, cut, RawCompressionStep.topProjectedStep,
            RawCompressionPath.ProjectedCompressionStep.cost]
  have htarget_parent :
      Gpad.parent targetNode = embed (D.topParent (seg.node last)) := by
    simpa [Gpad, G, hN, F, hF, hpack, D, e, embed, targetNode, last] using
      RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
        F hF hpack s (seg.node last)
  have htarget_ne : Gpad.parent targetNode ≠ targetNode := by
    intro hroot
    have hembed :
        embed (D.topParent (seg.node last)) = embed (seg.node last) := by
      simpa [targetNode] using htarget_parent.symm.trans hroot
    have htop_eq : D.topParent (seg.node last) = seg.node last := by
      apply e.injective
      apply Fin.ext
      change (e (D.topParent (seg.node last))).val = (e (seg.node last)).val
      exact congrArg (fun x : Fin N => x.val) hembed
    exact hseg_last_ne htop_eq
  have hP_nonroot : P.IsNonrootPath Gpad := by
    simpa [RawCompressionPath.IsNonrootPath, P, targetNode] using htarget_ne
  rcases RawCompressionPath.exists_valid_step_of_valid_nonroot_path
      Gpad P hP_valid hP_nonroot with ⟨S, hbefore, _hpath, hSvalid, hScost⟩
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · exact hSvalid
  · simpa [Gpad, G, hN, F, hF, hpack] using hbefore
  · exact hScost.trans hP_cost
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, Gpad, G, hN, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
          F hF hpack s
    exact hbeforePack
  · have hbeforePack : S.before.HasRankThresholdPacking := by
      simpa [hbefore, Gpad, G, hN, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
          F hF hpack s
    exact S.before.hasRankThresholdPacking_of_rankNat_eq S.after
      (fun v => by
        simp [RawRankedForest.rankNat, hSvalid.2.2.1 v])
      hbeforePack

/--
A charged rank-threshold top projected path lifts to a valid ordinary
compression path over the padded top budget.  The lifted path follows the
projected path and appends the top parent of the projected target; this gives
the ordinary source path the required two active slots even when the projected
edge cost is zero.
-/
theorem rankThreshold_topProjected_charged_path_lifts_to_padded_valid_path
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hcharged :
      ((E.step i).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged) :
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    Exists fun P : RawCompressionPath N =>
      P.IsValidFor (G.padRight hN) /\
        ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost <= P.cost := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let D := Dfam i
  let F := (E.step i).before
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hpack : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let G := RankThresholdDissection.topRestrictedForestFin F hF s
  let hN := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpack s
  let Gpad := G.padRight hN
  let seg := (E.step i).path.topProjectionSegment D (hE.1 i).1.2.2.1
    (cut i) (hcut i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, D, Dfam, cut, hcut, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hpos, _hlast_ne⟩
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, D, Dfam, cut, hcut, RawCompressionPath.topProjectionSegment]
      using hraw
  have hcard_le_budget : D.topFinset.card <= N := by
    simpa [N, D, Dfam, F, hF, hpack, G] using hN
  let e := D.topNodeEquivFin
  let embed : D.TopNode -> Fin N := fun v =>
    ⟨(e v).val, (e v).isLt.trans_le hcard_le_budget⟩
  let last : Fin seg.len := seg.lastIndex hpos
  let targetNode : Fin N := embed (D.topParent (seg.node last))
  let P : RawCompressionPath N := {
    len := ⟨seg.len + 1, by omega⟩
    node := fun j =>
      if hj : j.val < seg.len then embed (seg.node ⟨j.val, hj⟩)
      else targetNode
    target := targetNode
  }
  refine ⟨P, ?_, ?_⟩
  · refine ⟨?hrank, ?hlen, ?hchain, ?hlast⟩
    · simpa [Gpad, G, hN, F, hF, hpack] using
        RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
          F hF hpack s
    · simp [P]
      omega
    · intro a b hab hb
      by_cases hbseg : b.val < seg.len
      · have haseg : a.val < seg.len := by omega
        let aa : Fin seg.len := ⟨a.val, haseg⟩
        let bb : Fin seg.len := ⟨b.val, hbseg⟩
        have hparent_seg : D.topParent (seg.node aa) = seg.node bb := by
          exact seg.parent_chain (by simpa [aa, bb] using hab)
        have hparent_embed :
            Gpad.parent (embed (seg.node aa)) =
              embed (D.topParent (seg.node aa)) := by
          simpa [Gpad, G, hN, F, hF, hpack, D, e, embed] using
            RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
              F hF hpack s (seg.node aa)
        calc
          Gpad.parent (P.node a)
              = Gpad.parent (embed (seg.node aa)) := by
                  simp [P, aa, haseg]
          _ = embed (D.topParent (seg.node aa)) := hparent_embed
          _ = embed (seg.node bb) := by rw [hparent_seg]
          _ = P.node b := by
                  simp [P, bb, hbseg]
      · have hb_eq : b.val = seg.len := by
          have hb_len : b.val < seg.len + 1 := by simpa [P] using hb
          omega
        have haseg : a.val < seg.len := by omega
        let aa : Fin seg.len := ⟨a.val, haseg⟩
        have haa_last : aa = last := by
          apply Fin.ext
          simp [aa, last, RawCompressionPath.ProjectedPathSegment.lastIndex]
          omega
        have hparent_embed :
            Gpad.parent (embed (seg.node aa)) =
              embed (D.topParent (seg.node aa)) := by
          simpa [Gpad, G, hN, F, hF, hpack, D, e, embed] using
            RankThresholdDissection.topRestrictedForestFin_padded_parent_of_topNode
              F hF hpack s (seg.node aa)
        calc
          Gpad.parent (P.node a)
              = Gpad.parent (embed (seg.node aa)) := by
                  simp [P, aa, haseg]
          _ = embed (D.topParent (seg.node aa)) := hparent_embed
          _ = targetNode := by
                  simp [targetNode, haa_last]
          _ = P.node b := by
                  simp [P, hbseg]
    · intro a ha
      have hnot : Not (a.val < seg.len) := by
        intro hlt
        simp [P] at ha
        omega
      simp [P, hnot]
  · calc
      ((E.step i).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).cost
          = seg.edgeCost := by
              simp [seg, D, Dfam, cut, RawCompressionStep.topProjectedStep,
                RawCompressionPath.ProjectedCompressionStep.cost]
      _ <= seg.len := seg.edgeCost_le_len
      _ = P.cost := by
              simp [P, RawCompressionPath.cost]

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

/--
Rank-threshold top projected consumable cost is source-cost dominated.  This is
a genuine top-side simulation sanity check, but it is weaker than the
recurrence-consumed field of `RankThresholdLogConsumableBounds`.
-/
theorem rankThresholdTopProjectedExecution_consumableCost_le_cost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
      E.cost := by
  exact E.canonicalTopProjectedExecution_consumableCost_le_cost hE.1
    (E.rankThresholdDissectionFamily hE.1 s)

/--
Bottom rank-threshold projections are range-bounded stepwise: the total
consumable bottom cost is at most `s` times the bottom projected charged count.
-/
theorem rankThresholdBottomProjectedExecution_consumableCost_le_threshold_mul_chargedCount
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
      s *
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        ((E.step i).bottomProjectedStep (Dfam i) (hE.1 i) (cut i) (hcut i)).consumableCost)
        <=
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        s * ((E.step i).bottomProjectedStep
          (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      have hstep :=
        (E.step i).bottomProjectedStep_consumableCost_le_rankThreshold_mul_indicator
          (hE.1 i) s (cut i) (by
            simpa [Dfam, rankThresholdDissectionFamily] using hcut i)
      simpa [Dfam, rankThresholdDissectionFamily] using hstep)
  have hsum_eq :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        s * ((E.step i).bottomProjectedStep
          (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator)
        =
      s *
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
          ((E.step i).bottomProjectedStep
            (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator) := by
    rw [Finset.mul_sum]
  have hfinal := hsum.trans (le_of_eq hsum_eq)
  simpa [RawCompressionPath.ProjectedCompressionExecution.consumableCost,
    RawCompressionPath.ProjectedCompressionExecution.chargedCount,
    RawCompressionPath.ProjectedCompressionExecution.nonrootCount,
    canonicalBottomProjectedExecution, bottomProjectedExecution, Dfam, cut, hcut] using hfinal

/--
Top rank-threshold projections are range-bounded after the threshold shift:
the total consumable top cost is at most `(r - s - 1)` times the top projected
charged count.
-/
theorem rankThresholdTopProjectedExecution_consumableCost_le_shiftedRank_mul_chargedCount
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
      (r - s - 1) *
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        ((E.step i).topProjectedStep (Dfam i) (hE.1 i) (cut i) (hcut i)).consumableCost)
        <=
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        (r - s - 1) * ((E.step i).topProjectedStep
          (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      have hstep :=
        (E.step i).topProjectedStep_consumableCost_le_rankThreshold_mul_indicator
          (hE.1 i) s (cut i) (by
            simpa [Dfam, rankThresholdDissectionFamily] using hcut i)
      simpa [Dfam, rankThresholdDissectionFamily] using hstep)
  have hsum_eq :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
        (r - s - 1) * ((E.step i).topProjectedStep
          (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator)
        =
      (r - s - 1) *
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i =>
          ((E.step i).topProjectedStep
            (Dfam i) (hE.1 i) (cut i) (hcut i)).nonrootIndicator) := by
    rw [Finset.mul_sum]
  have hfinal := hsum.trans (le_of_eq hsum_eq)
  simpa [RawCompressionPath.ProjectedCompressionExecution.consumableCost,
    RawCompressionPath.ProjectedCompressionExecution.chargedCount,
    RawCompressionPath.ProjectedCompressionExecution.nonrootCount,
    canonicalTopProjectedExecution, topProjectedExecution, Dfam, cut, hcut] using hfinal

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

/--
All compacted charged bottom slots use the same bottom vertex set cardinality
as any chosen reference slot.
-/
theorem rankThresholdBottomChargedSlot_bottomFinset_card_eq_of_slot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    (E.rankThresholdDissectionFamily hE.1 s
        (E.rankThresholdBottomChargedSlot hE s q)).bottomFinset.card =
      (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card := by
  have hfinset :
      (E.rankThresholdDissectionFamily hE.1 s
          (E.rankThresholdBottomChargedSlot hE s q)).bottomFinset =
        (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset :=
    E.rankThresholdDissectionFamily_bottomFinset_eq_of_slot
      hE.1 hE.2.1 s i0 (E.rankThresholdBottomChargedSlot hE s q)
  exact congrArg Finset.card hfinset

/--
Ordinary bottom charged execution skeleton over a fixed reference bottom
cardinality.  The steps are the chosen per-slot bottom realizations, cast along
the stable bottom-cardinality equality.  This skeleton has valid slots and the
right cost; consecutive state alignment is the remaining bridge.
-/
noncomputable def rankThresholdBottomChargedExecutionSkeleton
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    RawCompressionExecution
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)
      s where
  step := fun q =>
    (E.rankThresholdBottomChargedStep hE s q).castVertexCount
      (E.rankThresholdBottomChargedSlot_bottomFinset_card_eq_of_slot hE s i0 q)

/-- The bottom charged execution skeleton has valid ordinary source steps. -/
theorem rankThresholdBottomChargedExecutionSkeleton_hasValidSteps
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    (E.rankThresholdBottomChargedExecutionSkeleton hE s i0).HasValidSteps := by
  intro q
  have hspec := E.rankThresholdBottomChargedStep_spec hE s q
  exact RawCompressionStep.castVertexCount_isValid
    (E.rankThresholdBottomChargedStep hE s q)
    (E.rankThresholdBottomChargedSlot_bottomFinset_card_eq_of_slot hE s i0 q)
    hspec.1

/-- The bottom charged execution skeleton has rank-threshold packing at endpoints. -/
theorem rankThresholdBottomChargedExecutionSkeleton_hasRankThresholdPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    (E.rankThresholdBottomChargedExecutionSkeleton hE s i0).HasRankThresholdPacking := by
  intro q
  have hspec := E.rankThresholdBottomChargedStep_spec hE s q
  constructor
  · exact RawCompressionStep.castVertexCount_before_hasRankThresholdPacking
      (E.rankThresholdBottomChargedStep hE s q)
      (E.rankThresholdBottomChargedSlot_bottomFinset_card_eq_of_slot hE s i0 q)
      hspec.2.2.2.1
  · exact RawCompressionStep.castVertexCount_after_hasRankThresholdPacking
      (E.rankThresholdBottomChargedStep hE s q)
      (E.rankThresholdBottomChargedSlot_bottomFinset_card_eq_of_slot hE s i0 q)
      hspec.2.2.2.2

/-- Cost of a bottom skeleton slot matches the corresponding charged projected slot. -/
theorem rankThresholdBottomChargedExecutionSkeleton_step_cost_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (q : Fin
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    ((E.rankThresholdBottomChargedExecutionSkeleton hE s i0).step q).cost =
      ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost := by
  have hspec := E.rankThresholdBottomChargedStep_spec hE s q
  calc
    ((E.rankThresholdBottomChargedExecutionSkeleton hE s i0).step q).cost =
        (E.rankThresholdBottomChargedStep hE s q).cost := by
          simp [rankThresholdBottomChargedExecutionSkeleton]
    _ = ((E.rankThresholdBottomChargedProjectedExecution hE s).step q).cost :=
        hspec.2.2.1

/-- The bottom charged execution skeleton has exactly the bottom consumable cost. -/
theorem rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    (E.rankThresholdBottomChargedExecutionSkeleton hE s i0).cost =
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
  classical
  let Ebot := E.rankThresholdBottomChargedExecutionSkeleton hE s i0
  let Cbc := E.rankThresholdBottomChargedProjectedExecution hE s
  calc
    Ebot.cost = Ebot.stepCostSum := Ebot.cost_eq_stepCostSum
    _ = Cbc.cost := by
      unfold stepCostSum RawCompressionPath.ProjectedCompressionExecution.cost
      apply Finset.sum_congr rfl
      intro q _hq
      simpa [Ebot, Cbc] using
        E.rankThresholdBottomChargedExecutionSkeleton_step_cost_eq hE s i0 q
    _ =
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
      simpa [Cbc] using
        E.rankThresholdBottomChargedProjectedExecution_cost_eq_consumableCost hE s

/--
Conditional bottom consumption theorem for the charged skeleton.  The only
missing semantic ingredient is literal consecutive-state alignment after the
per-slot bottom cardinality casts.
-/
theorem rankThresholdBottomProjectedExecution_consumableCost_le_topDownCost_bottomCard_of_skeleton_consecutive
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hstate :
      (E.rankThresholdBottomChargedExecutionSkeleton hE s i0).HasConsecutiveStates) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost <= topDownCost Cb.chargedCount Bcard s := by
  classical
  intro Cb Bcard
  let Ebot := E.rankThresholdBottomChargedExecutionSkeleton hE s i0
  have hsemantic : Ebot.IsSemanticallyValid :=
    ⟨E.rankThresholdBottomChargedExecutionSkeleton_hasValidSteps hE s i0, hstate⟩
  have hbase : Ebot.HasBaseRankAccounting :=
    ⟨Ebot.hasLegacyBaseRankAccounting_of_semanticallyValid hsemantic,
      E.rankThresholdBottomChargedExecutionSkeleton_hasRankThresholdPacking hE s i0⟩
  have hvalid : Ebot.IsValid :=
    Ebot.isValid_of_semantic_and_rank hsemantic hbase
  have hcost :
      Ebot.cost <= topDownCost Cb.chargedCount Bcard s := by
    simpa [Ebot, Cb, Bcard] using Ebot.cost_le_topDownCost hvalid
  have hcost_eq :
      Ebot.cost = Cb.consumableCost := by
    simpa [Ebot, Cb] using
      E.rankThresholdBottomChargedExecutionSkeleton_cost_eq_consumableCost hE s i0
  simpa [hcost_eq] using hcost

/--
Source-relevant bottom boundary-exception slots.  These are precisely the
rank-threshold bottom slots whose source step is a nonroot step, whose bottom
projection is not charged, and whose bottom prefix contains at least one edge.
Such slots are the uncharged boundary transitions counted by the existing
source-relevant bottom exceptional-cost accounting.
-/
def rankThresholdBottomBoundaryExceptionSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) : Prop :=
  (E.step i).path.IsNonrootPath (E.step i).before /\
    Not ((E.step i).bottomProjectedStep
      (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
      (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
      (E.dissectionCut_spec hE.1
        (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged /\
    Exists fun q : Fin (n + 1) =>
      q.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i

/--
Boundary-inclusive bottom slots: either charged bottom slots, or
source-relevant uncharged bottom boundary-exception slots.
-/
def rankThresholdBottomRelevantSlot
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) : Prop :=
  ((E.canonicalBottomProjectedExecution hE.1
    (E.rankThresholdDissectionFamily hE.1 s)).step i).IsCharged \/
    E.rankThresholdBottomBoundaryExceptionSlot hE s i

noncomputable def rankThresholdBottomRelevantFinset
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => E.rankThresholdBottomRelevantSlot hE s i

@[simp]
theorem mem_rankThresholdBottomRelevantFinset
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    i ∈ E.rankThresholdBottomRelevantFinset hE s <->
      E.rankThresholdBottomRelevantSlot hE s i := by
  classical
  simp [rankThresholdBottomRelevantFinset]

noncomputable def rankThresholdBottomRelevantCount
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) : Nat :=
  (E.rankThresholdBottomRelevantFinset hE s).card

theorem rankThresholdBottomRelevantFinset_card_eq_count
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdBottomRelevantFinset hE s).card =
      E.rankThresholdBottomRelevantCount hE s := rfl

/-- Increasing enumeration of the boundary-inclusive bottom relevant slots. -/
noncomputable def rankThresholdBottomRelevantSlotEnum
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fin (E.rankThresholdBottomRelevantCount hE s) -> Fin m :=
  (E.rankThresholdBottomRelevantFinset hE s).orderEmbOfFin
    (E.rankThresholdBottomRelevantFinset_card_eq_count hE s)

@[simp]
theorem rankThresholdBottomRelevantSlotEnum_mem
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin (E.rankThresholdBottomRelevantCount hE s)) :
    E.rankThresholdBottomRelevantSlotEnum hE s q ∈
      E.rankThresholdBottomRelevantFinset hE s := by
  simp [rankThresholdBottomRelevantSlotEnum]

theorem rankThresholdBottomRelevantSlotEnum_isRelevant
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin (E.rankThresholdBottomRelevantCount hE s)) :
    E.rankThresholdBottomRelevantSlot hE s
      (E.rankThresholdBottomRelevantSlotEnum hE s q) := by
  exact (E.mem_rankThresholdBottomRelevantFinset hE s
    (E.rankThresholdBottomRelevantSlotEnum hE s q)).1
      (E.rankThresholdBottomRelevantSlotEnum_mem hE s q)

theorem rankThresholdBottomRelevantSlotEnum_strictMono
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    StrictMono (E.rankThresholdBottomRelevantSlotEnum hE s) := by
  intro q q' hlt
  exact ((E.rankThresholdBottomRelevantFinset hE s).orderEmbOfFin
    (E.rankThresholdBottomRelevantFinset_card_eq_count hE s)).strictMono hlt

theorem rankThresholdBottomRelevantSlot_of_charged
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i : Fin m}
    (hcharged :
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).step i).IsCharged) :
    E.rankThresholdBottomRelevantSlot hE s i := by
  exact Or.inl hcharged

theorem rankThresholdBottomRelevantSlot_of_boundaryException
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i : Fin m}
    (hboundary : E.rankThresholdBottomBoundaryExceptionSlot hE s i) :
    E.rankThresholdBottomRelevantSlot hE s i := by
  exact Or.inr hboundary

/--
There are no boundary-inclusive relevant slots strictly between adjacent
entries of the relevant-slot enumeration.
-/
theorem not_rankThresholdBottomRelevantSlot_of_between_relevantSlotEnum_succ
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {q q' : Fin (E.rankThresholdBottomRelevantCount hE s)}
    (hqq' : q.val + 1 = q'.val)
    (i : Fin m)
    (hleft : (E.rankThresholdBottomRelevantSlotEnum hE s q).val < i.val)
    (hright : i.val < (E.rankThresholdBottomRelevantSlotEnum hE s q').val) :
    Not (E.rankThresholdBottomRelevantSlot hE s i) := by
  classical
  intro hrel
  have hi_mem : i ∈ E.rankThresholdBottomRelevantFinset hE s :=
    (E.mem_rankThresholdBottomRelevantFinset hE s i).2 hrel
  have hi_range :
      i ∈ Set.range
        ((E.rankThresholdBottomRelevantFinset hE s).orderEmbOfFin
          (E.rankThresholdBottomRelevantFinset_card_eq_count hE s)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi_mem
  rcases hi_range with ⟨p, hp⟩
  have hp_eq : E.rankThresholdBottomRelevantSlotEnum hE s p = i := by
    simpa [rankThresholdBottomRelevantSlotEnum] using hp
  have hq_lt_p : q.val < p.val := by
    by_contra hnot
    have hp_le_q : p.val <= q.val := by omega
    by_cases hpq : p.val = q.val
    · have hp_fin : p = q := Fin.ext hpq
      subst p
      rw [hp_eq] at hleft
      exact (Nat.lt_irrefl _) hleft
    · have hp_lt_q : p.val < q.val := by omega
      have hslot_lt :
          (E.rankThresholdBottomRelevantSlotEnum hE s p).val <
            (E.rankThresholdBottomRelevantSlotEnum hE s q).val :=
        E.rankThresholdBottomRelevantSlotEnum_strictMono hE s hp_lt_q
      rw [hp_eq] at hslot_lt
      omega
  have hp_lt_q' : p.val < q'.val := by
    by_contra hnot
    have hq'_le_p : q'.val <= p.val := by omega
    by_cases hpq' : p.val = q'.val
    · have hp_fin : p = q' := Fin.ext hpq'
      subst p
      rw [hp_eq] at hright
      exact (Nat.lt_irrefl _) hright
    · have hq'_lt_p : q'.val < p.val := by omega
      have hslot_lt :
          (E.rankThresholdBottomRelevantSlotEnum hE s q').val <
            (E.rankThresholdBottomRelevantSlotEnum hE s p).val :=
        E.rankThresholdBottomRelevantSlotEnum_strictMono hE s hq'_lt_p
      rw [hp_eq] at hslot_lt
      omega
  omega

/--
Slots omitted by the boundary-inclusive bottom relevant-slot enumeration are
literal no-ops on the bottom restricted parent map.  This is the local
commutation fact needed to skip non-relevant slots between consecutive relevant
bottom slots.
-/
theorem rankThresholdBottomProjectedStep_afterParent_eq_beforeParent_of_not_relevant
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m)
    (hnot : Not (E.rankThresholdBottomRelevantSlot hE s i)) :
    ((E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).step i).afterParent =
      ((E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).step i).beforeParent := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  have hnotBoundary :
      Not ((E.step i).path.IsNonrootPath (E.step i).before /\
        Exists fun q : Fin (n + 1) => q.val + 1 < cut i) := by
    intro hb
    have hnotCharged :
        Not ((E.step i).bottomProjectedStep (Dfam i) (hE.1 i)
          (cut i) (hcut i)).IsCharged := by
      intro hcharged
      apply hnot
      exact Or.inl (by
        simpa [Dfam, cut, hcut, canonicalBottomProjectedExecution,
          bottomProjectedExecution] using hcharged)
    apply hnot
    exact Or.inr ⟨hb.1, by
      simpa [Dfam, cut, hcut] using hnotCharged, hb.2⟩
  have hlocal :=
    (E.step i).bottomProjectedStep_afterParent_eq_beforeParent_of_no_sourceBoundary
      (Dfam i) (hE.1 i) (cut i) (hcut i) hnotBoundary
  simpa [Dfam, cut, hcut, canonicalBottomProjectedExecution,
    bottomProjectedExecution] using hlocal

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

/-- Rank-threshold top-side predicates are stable across all execution slots. -/
theorem rankThresholdDissectionFamily_topStable_of_slot
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i0 i : Fin m)
    (v : Fin n) :
    Iff ((E.rankThresholdDissectionFamily hsteps s i0).IsTop v)
      ((E.rankThresholdDissectionFamily hsteps s i).IsTop v) := by
  unfold rankThresholdDissectionFamily
  simp only [RankThresholdDissection.dissection_isTop]
  rw [E.rankThresholdDissectionFamily_rankNat_eq_of_slot
    hsteps hstate i0 i v]

/--
If all top projected slots strictly between `i` and `j` are uncharged, then
the top parent map after slot `i` agrees with the top parent map before slot
`j` on vertices from the stable top side.
-/
theorem rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i j : Fin m}
    (hij : i.val < j.val)
    (hskip :
      forall k : Fin m, i.val < k.val -> k.val < j.val ->
        Not ((E.step k).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s k) (hE.1 k)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) k)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) k)).IsCharged)
    (v : (E.rankThresholdDissectionFamily hE.1 s i).TopNode) :
    (E.step i).after.parent v.1 = (E.step j).before.parent v.1 := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  let base := i.val + 1
  have hbase_le_j : base <= j.val := by
    simpa [base] using Nat.succ_le_of_lt hij
  have hbase_lt_m : base < m := by
    omega
  have hmain :
      forall d : Nat, forall hle : base + d <= j.val,
        (E.step i).after.parent v.1 =
          (E.step ⟨base + d, by omega⟩).before.parent v.1 := by
    intro d
    induction d with
    | zero =>
        intro _hle
        let next : Fin m := ⟨base, hbase_lt_m⟩
        have hstate_i_next : (E.step i).after = (E.step next).before :=
          hE.2.1 i next (by simp [next, base])
        simp [next, base, hstate_i_next]
    | succ d ih =>
        intro hle
        let prev : Fin m := ⟨base + d, by omega⟩
        let curr : Fin m := ⟨base + (d + 1), by omega⟩
        have hprev_lt_j : prev.val < j.val := by
          simp [prev] at hle ⊢
          omega
        have hi_lt_prev : i.val < prev.val := by
          simp [prev, base]
          omega
        have hnot_prev :
            Not ((E.step prev).topProjectedStep
              (Dfam prev) (hE.1 prev) (cut prev) (hcut prev)).IsCharged := by
          simpa [Dfam, cut, hcut] using hskip prev hi_lt_prev hprev_lt_j
        have hpersist :
            (E.step i).after.parent v.1 =
              (E.step prev).before.parent v.1 := by
          simpa [prev] using ih (by omega)
        have htop_prev : (Dfam prev).IsTop v.1 :=
          (E.rankThresholdDissectionFamily_topStable_of_slot
            hE.1 hE.2.1 s i prev v.1).1 v.2
        let w : (Dfam prev).TopNode := ⟨v.1, htop_prev⟩
        have hidentity :
            (E.step prev).after.parent v.1 =
              (E.step prev).before.parent v.1 := by
          have hfun :=
            congrFun
              ((E.step prev).topProjectedStep_afterParent_eq_beforeParent_of_not_charged
                (Dfam prev) (hE.1 prev) (cut prev) (hcut prev) hnot_prev) w
          have hval := congrArg Subtype.val hfun
          simpa [RawCompressionStep.topProjectedStep, RawCompressionStep.afterTopParent,
            RawDissection.topParent, w] using hval
        have hstate_prev_curr :
            (E.step prev).after = (E.step curr).before := by
          exact hE.2.1 prev curr (by simp [prev, curr, base]; omega)
        have hcurr :
            (E.step prev).after.parent v.1 =
              (E.step curr).before.parent v.1 := by
          rw [hstate_prev_curr]
        calc
          (E.step i).after.parent v.1
              = (E.step prev).before.parent v.1 := hpersist
          _ = (E.step prev).after.parent v.1 := hidentity.symm
          _ = (E.step curr).before.parent v.1 := hcurr
  have hfinal := hmain (j.val - base) (by omega)
  simpa [base, Nat.add_sub_of_le hbase_le_j] using hfinal

/--
Projected-step form of
`rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between`.
It is the consecutive-state bridge needed when a charged-only top execution
skips uncharged top projected slots.
-/
theorem rankThresholdTopProjectedStep_after_commutes_with_later_before_of_not_charged_between
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {i j : Fin m}
    (hij : i.val < j.val)
    (hskip :
      forall k : Fin m, i.val < k.val -> k.val < j.val ->
        Not ((E.step k).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s k) (hE.1 k)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) k)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) k)).IsCharged) :
    ((E.step i).topProjectedStep
      (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
      (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
      (E.dissectionCut_spec hE.1
        (E.rankThresholdDissectionFamily hE.1 s) i)).ParentCommutesWithEquiv
      ((E.step j).topProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s j) (hE.1 j)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) j)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) j))
      ((E.rankThresholdDissectionFamily hE.1 s i).topEquivOfTopIff
        (E.rankThresholdDissectionFamily hE.1 s j)
        (E.rankThresholdDissectionFamily_topStable_of_slot
          hE.1 hE.2.1 s i j)) := by
  intro v
  apply Subtype.ext
  have hparent :=
    E.rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between
      hE s hij hskip v
  simpa [RawCompressionStep.topProjectedStep, RawCompressionStep.afterTopParent,
    RawDissection.topParent, RawDissection.topEquivOfTopIff] using hparent

/--
Adjacent compacted charged slots of the rank-threshold top projection have
consecutive states after skipping the intervening uncharged top slots.
-/
theorem rankThresholdTopChargedSlot_after_commutes_with_next
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {q q' : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)}
    (hqq' : q.val + 1 = q'.val) :
    let Dfam := E.rankThresholdDissectionFamily hE.1 s
    let i := E.rankThresholdTopChargedSlot hE s q
    let j := E.rankThresholdTopChargedSlot hE s q'
    ((E.step i).topProjectedStep
      (Dfam i) (hE.1 i)
      (E.dissectionCut hE.1 Dfam i)
      (E.dissectionCut_spec hE.1 Dfam i)).ParentCommutesWithEquiv
      ((E.step j).topProjectedStep
        (Dfam j) (hE.1 j)
        (E.dissectionCut hE.1 Dfam j)
        (E.dissectionCut_spec hE.1 Dfam j))
      ((Dfam i).topEquivOfTopIff (Dfam j)
        (E.rankThresholdDissectionFamily_topStable_of_slot
          hE.1 hE.2.1 s i j)) := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let Ct := E.canonicalTopProjectedExecution hE.1 Dfam
  let i := E.rankThresholdTopChargedSlot hE s q
  let j := E.rankThresholdTopChargedSlot hE s q'
  have hq_lt_q' : q.val < q'.val := by omega
  have hij : i.val < j.val := by
    simpa [i, j] using E.rankThresholdTopChargedSlot_strictMono hE s hq_lt_q'
  refine
    E.rankThresholdTopProjectedStep_after_commutes_with_later_before_of_not_charged_between
      hE s hij ?_
  intro k hkleft hkright
  have hleft : (Ct.chargedSlot q).val < k.val := by
    simpa [Ct, i, rankThresholdTopChargedSlot] using hkleft
  have hright : k.val < (Ct.chargedSlot q').val := by
    simpa [Ct, j, rankThresholdTopChargedSlot] using hkright
  have hnotCt : Not (Ct.step k).IsCharged :=
    Ct.not_isCharged_of_between_chargedSlot_succ hqq' k hleft hright
  simpa [Ct, Dfam, canonicalTopProjectedExecution, topProjectedExecution] using hnotCt

/--
Dependent projected execution consisting only of the charged slots of the
rank-threshold top projection.
-/
noncomputable def rankThresholdTopChargedProjectedExecution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    RawCompressionPath.ProjectedCompressionExecution
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount) := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  exact {
    vertex := fun q => (Dfam (E.rankThresholdTopChargedSlot hE s q)).TopNode
    step := fun q =>
      (E.step (E.rankThresholdTopChargedSlot hE s q)).topProjectedStep
        (Dfam (E.rankThresholdTopChargedSlot hE s q))
        (hE.1 (E.rankThresholdTopChargedSlot hE s q))
        (E.dissectionCut hE.1 Dfam (E.rankThresholdTopChargedSlot hE s q))
        (E.dissectionCut_spec hE.1 Dfam
          (E.rankThresholdTopChargedSlot hE s q))
  }

/-- The charged top projected execution has consecutive states. -/
theorem rankThresholdTopChargedProjectedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedProjectedExecution hE s).HasConsecutiveStates := by
  intro q q' hqq'
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  let j := E.rankThresholdTopChargedSlot hE s q'
  refine ⟨(Dfam i).topEquivOfTopIff (Dfam j)
    (E.rankThresholdDissectionFamily_topStable_of_slot hE.1 hE.2.1 s i j), ?_⟩
  simpa [rankThresholdTopChargedProjectedExecution, Dfam, i, j] using
    E.rankThresholdTopChargedSlot_after_commutes_with_next hE s hqq'

/-- The charged top projected execution is semantically valid in the projected API. -/
theorem rankThresholdTopChargedProjectedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedProjectedExecution hE s).IsSemanticallyValid :=
  E.rankThresholdTopChargedProjectedExecution_hasConsecutiveStates hE s

/-- The charged top projected execution is admissible in the projected API. -/
theorem rankThresholdTopChargedProjectedExecution_isAdmissible
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedProjectedExecution hE s).IsAdmissible :=
  E.rankThresholdTopChargedProjectedExecution_isSemanticallyValid hE s

/-- The charged top projected execution cost is the original top consumable cost. -/
theorem rankThresholdTopChargedProjectedExecution_cost_eq_consumableCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedProjectedExecution hE s).cost =
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let Ct := E.canonicalTopProjectedExecution hE.1 Dfam
  simpa [rankThresholdTopChargedProjectedExecution, rankThresholdTopChargedSlot,
    RawCompressionPath.ProjectedCompressionExecution.chargedSubexecution,
    Ct, Dfam, canonicalTopProjectedExecution, topProjectedExecution]
    using Ct.chargedSubexecution_cost_eq_consumableCost

/--
At a compacted charged top slot, a zero projected edge cost is exactly the
case that can be skipped at the projected parent-map level: the projected
after-parent is the same function as the projected before-parent.
-/
theorem rankThresholdTopChargedSlot_zero_cost_afterParent_eq_beforeParent
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hcost :
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost = 0) :
    ((E.rankThresholdTopChargedProjectedExecution hE s).step q).afterParent =
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).beforeParent := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  have hcost_i :
      ((E.step i).topProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).cost = 0 := by
    simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using hcost
  have hidentity :=
    (E.step i).topProjectedStep_afterParent_eq_beforeParent_of_cost_eq_zero
      (Dfam i) (hE.1 i)
      (E.dissectionCut hE.1 Dfam i)
      (E.dissectionCut_spec hE.1 Dfam i) hcost_i
  simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using hidentity

/--
Zero-cost compacted charged top slots are skipped literally after padding:
their padded after top restriction is the same forest as their padded before top
restriction over the external top budget.
-/
theorem rankThresholdTopChargedSlot_zero_cost_padded_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hcost :
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost = 0) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let hBeforeRank : (E.step i).before.IsRankValid := (hE.1 i).1.1
    let hAfterRank : (E.step i).after.IsRankValid := (hE.1 i).2.1
    let hBeforePack : (E.step i).before.HasRankThresholdPacking :=
      (E.hasRankThresholdPacking_of_isValid hE i).1
    let hAfterPack : (E.step i).after.HasRankThresholdPacking :=
      (E.hasRankThresholdPacking_of_isValid hE i).2
    (RankThresholdDissection.topRestrictedForestFin
        (E.step i).after hAfterRank s).padRight
        (RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).after hAfterRank hAfterPack s) =
      (RankThresholdDissection.topRestrictedForestFin
        (E.step i).before hBeforeRank s).padRight
        (RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).before hBeforeRank hBeforePack s) := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  let D := Dfam i
  have hzero_i :
      ((E.step i).topProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).afterParent =
        ((E.step i).topProjectedStep
          (Dfam i) (hE.1 i)
          (E.dissectionCut hE.1 Dfam i)
          (E.dissectionCut_spec hE.1 Dfam i)).beforeParent := by
    simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using
      E.rankThresholdTopChargedSlot_zero_cost_afterParent_eq_beforeParent
        hE s q hcost
  have hrank :
      forall v : Fin n,
        (E.step i).after.rankNat v = (E.step i).before.rankNat v := by
    intro v
    unfold RawRankedForest.rankNat
    exact congrArg Fin.val ((hE.1 i).2.2.1 v)
  have hparent :
      forall x : D.TopNode,
        (E.step i).after.parent x.1 = (E.step i).before.parent x.1 := by
    intro x
    have hx := congrArg Subtype.val (congrFun hzero_i x)
    simpa [D, Dfam, RawCompressionStep.topProjectedStep,
      RawCompressionStep.afterTopParent, RawDissection.topParent] using hx
  simpa [Dfam, i, rankThresholdDissectionFamily] using
    RankThresholdDissection.topRestrictedForestFin_padded_eq_of_rankNat_eq_of_top_parent_eq
      (E.step i).before (E.step i).after
      (hE.1 i).1.1 (hE.1 i).2.1
      ((E.hasRankThresholdPacking_of_isValid hE i).1)
      ((E.hasRankThresholdPacking_of_isValid hE i).2)
      s hrank hparent

/--
Positive-cost compacted charged top slots lift to valid ordinary padded source
steps over the external top budget.  This is the charged-slot-indexed wrapper
around the local positive-step realization theorem.
-/
theorem rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hpos :
      0 <
        ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let G :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hN :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = G.padRight hN /\
          S.cost =
            ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking := by
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  have hcharged :
      ((E.step i).topProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).IsCharged := by
    simpa [Dfam, i] using E.rankThresholdTopChargedSlot_isCharged hE s q
  have hpos_i :
      0 <
        ((E.step i).topProjectedStep
          (Dfam i) (hE.1 i)
          (E.dissectionCut hE.1 Dfam i)
          (E.dissectionCut_spec hE.1 Dfam i)).cost := by
    simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using hpos
  simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using
    E.rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step
      hE s i hcharged hpos_i

/--
Positive-cost compacted charged top slots lift to valid ordinary padded source
steps with exact before, after, and path equalities.
-/
theorem rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step_with_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hpos :
      0 <
        ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = Gbefore.padRight hNbefore /\
          S.after = Gafter.padRight hNafter /\
            S.path = E.rankThresholdTopProjectedPaddedPath hE s i
              (by
                simpa [i] using E.rankThresholdTopChargedSlot_isCharged hE s q) /\
              S.cost =
                ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
                S.before.HasRankThresholdPacking /\
                  S.after.HasRankThresholdPacking := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  have hcharged :
      ((E.step i).topProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).IsCharged := by
    simpa [Dfam, i] using E.rankThresholdTopChargedSlot_isCharged hE s q
  have hpos_i :
      0 <
        ((E.step i).topProjectedStep
          (Dfam i) (hE.1 i)
          (E.dissectionCut hE.1 Dfam i)
          (E.dissectionCut_spec hE.1 Dfam i)).cost := by
    simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using hpos
  simpa [rankThresholdTopChargedProjectedExecution, Dfam, i] using
    E.rankThreshold_topProjected_charged_positive_step_lifts_to_padded_valid_step_with_state_eq
      hE s i hcharged hpos_i

/--
Adjacent compacted charged top slots align as literal padded source forests:
the padded top restriction after the earlier charged slot is the padded top
restriction before the next charged slot.
-/
theorem rankThresholdTopChargedSlot_padded_after_eq_next_before
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    {q q' : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)}
    (hqq' : q.val + 1 = q'.val) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let j := E.rankThresholdTopChargedSlot hE s q'
    let hAfterRank : (E.step i).after.IsRankValid := (hE.1 i).2.1
    let hBeforeRank : (E.step j).before.IsRankValid := (hE.1 j).1.1
    let hAfterPack : (E.step i).after.HasRankThresholdPacking :=
      (E.hasRankThresholdPacking_of_isValid hE i).2
    let hBeforePack : (E.step j).before.HasRankThresholdPacking :=
      (E.hasRankThresholdPacking_of_isValid hE j).1
    (RankThresholdDissection.topRestrictedForestFin
        (E.step i).after hAfterRank s).padRight
        (RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).after hAfterRank hAfterPack s) =
      (RankThresholdDissection.topRestrictedForestFin
        (E.step j).before hBeforeRank s).padRight
        (RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step j).before hBeforeRank hBeforePack s) := by
  classical
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let Ct := E.canonicalTopProjectedExecution hE.1 Dfam
  let i := E.rankThresholdTopChargedSlot hE s q
  let j := E.rankThresholdTopChargedSlot hE s q'
  have hq_lt_q' : q.val < q'.val := by omega
  have hij : i.val < j.val := by
    simpa [i, j] using E.rankThresholdTopChargedSlot_strictMono hE s hq_lt_q'
  have hskip :
      forall k : Fin m, i.val < k.val -> k.val < j.val ->
        Not ((E.step k).topProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s k) (hE.1 k)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) k)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) k)).IsCharged := by
    intro k hkleft hkright
    have hleft : (Ct.chargedSlot q).val < k.val := by
      simpa [Ct, Dfam, i, rankThresholdTopChargedSlot] using hkleft
    have hright : k.val < (Ct.chargedSlot q').val := by
      simpa [Ct, Dfam, j, rankThresholdTopChargedSlot] using hkright
    have hnotCt : Not (Ct.step k).IsCharged :=
      Ct.not_isCharged_of_between_chargedSlot_succ hqq' k hleft hright
    simpa [Ct, Dfam, canonicalTopProjectedExecution, topProjectedExecution] using hnotCt
  have hrank :
      forall v : Fin n,
        (E.step i).after.rankNat v = (E.step j).before.rankNat v := by
    intro v
    calc
      (E.step i).after.rankNat v = (E.step i).before.rankNat v := by
        unfold RawRankedForest.rankNat
        exact congrArg Fin.val ((hE.1 i).2.2.1 v)
      _ = (E.step j).before.rankNat v := by
        exact (E.rankThresholdDissectionFamily_rankNat_eq_of_slot
          hE.1 hE.2.1 i j v).symm
  have hparent :
      forall x : (RankThresholdDissection.dissection
          (E.step j).before (hE.1 j).1.1 s).TopNode,
        (E.step i).after.parent x.1 = (E.step j).before.parent x.1 := by
    intro x
    have htop_i : (Dfam i).IsTop x.1 := by
      exact (E.rankThresholdDissectionFamily_topStable_of_slot
        hE.1 hE.2.1 s j i x.1).1 x.2
    let xi : (Dfam i).TopNode := ⟨x.1, htop_i⟩
    have hraw :=
      E.rankThresholdTopParent_eq_later_beforeParent_of_not_charged_between
        hE s hij hskip xi
    simpa [Dfam, xi] using hraw
  simpa [Dfam, i, j, rankThresholdDissectionFamily] using
    RankThresholdDissection.topRestrictedForestFin_padded_eq_of_rankNat_eq_of_top_parent_eq
      (E.step j).before (E.step i).after
      (hE.1 j).1.1 (hE.1 i).2.1
      ((E.hasRankThresholdPacking_of_isValid hE j).1)
      ((E.hasRankThresholdPacking_of_isValid hE i).2)
      s hrank hparent

/--
Zero-cost compacted charged top slots are packaged as ordinary zero-cost
rootpath no-op steps over the padded top budget.
-/
theorem rankThresholdTopChargedSlot_zero_cost_lifts_to_padded_noop_step
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount))
    (hcost :
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost = 0) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = Gbefore.padRight hNbefore /\
          S.after = Gafter.padRight hNafter /\
            S.cost =
              ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  let N := RankThresholdDissection.topRestrictedBudget (n := n) s
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let i := E.rankThresholdTopChargedSlot hE s q
  let F := (E.step i).before
  let A := (E.step i).after
  let hF : F.IsRankValid := (hE.1 i).1.1
  let hA : A.IsRankValid := (hE.1 i).2.1
  let hpackF : F.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).1
  let hpackA : A.HasRankThresholdPacking :=
    (E.hasRankThresholdPacking_of_isValid hE i).2
  let Gbefore := RankThresholdDissection.topRestrictedForestFin F hF s
  let hNbefore := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    F hF hpackF s
  let Gafter := RankThresholdDissection.topRestrictedForestFin A hA s
  let hNafter := RankThresholdDissection.topRestrictedForestFin_card_le_budget
    A hA hpackA s
  let Gpad := Gbefore.padRight hNbefore
  have hcharged :
      ((E.step i).topProjectedStep
        (Dfam i) (hE.1 i)
        (E.dissectionCut hE.1 Dfam i)
        (E.dissectionCut_spec hE.1 Dfam i)).IsCharged := by
    simpa [Dfam, i] using E.rankThresholdTopChargedSlot_isCharged hE s q
  let seg := (E.step i).path.topProjectionSegment (Dfam i)
    (hE.1 i).1.2.2.1
    (E.dissectionCut hE.1 Dfam i)
    (E.dissectionCut_spec hE.1 Dfam i)
  have hseg_nonroot : seg.IsNonrootPath := by
    simpa [seg, Dfam, RawCompressionStep.topProjectedStep,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath] using hcharged
  rcases hseg_nonroot with ⟨hseg_pos, _hseg_nonroot⟩
  have hlen_budget : seg.len <= N := by
    have hraw :=
      E.rankThresholdTopProjectedStep_topProjectionLength_le_topBudget_of_charged
        hE s i hcharged
    simpa [N, seg, Dfam, RawCompressionPath.topProjectionSegment] using hraw
  have hNpos : 0 < N := by omega
  have hGpad_rank : Gpad.IsRankValid := by
    simpa [Gpad, Gbefore, hNbefore, F, hF, hpackF] using
      RankThresholdDissection.topRestrictedForestFin_padded_isRankValid
        F hF hpackF s
  rcases RawCompressionStep.exists_valid_zero_cost_noop_step
      Gpad hGpad_rank hNpos with ⟨S, hSvalid, hSbefore, hSafter, hScost⟩
  have hstate :
      Gafter.padRight hNafter = Gbefore.padRight hNbefore := by
    simpa [F, A, hF, hA, hpackF, hpackA, Gbefore, hNbefore, Gafter, hNafter, i]
      using E.rankThresholdTopChargedSlot_zero_cost_padded_state_eq hE s q hcost
  refine ⟨S, hSvalid, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Gpad, Gbefore, hNbefore] using hSbefore
  · calc
      S.after = Gbefore.padRight hNbefore := by
        simpa [Gpad, Gbefore, hNbefore] using hSafter
      _ = Gafter.padRight hNafter := hstate.symm
  · rw [hScost, hcost]
  · rw [hSbefore]
    simpa [Gpad, Gbefore, hNbefore] using
      RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
        F hF hpackF s
  · rw [hSafter]
    simpa [Gpad, Gbefore, hNbefore] using
      RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
        F hF hpackF s

/--
Every compacted charged top slot, positive or zero cost, has an ordinary padded
source step with exact padded before/after forests and matching slot cost.
-/
theorem rankThresholdTopChargedSlot_lifts_to_padded_step_with_state_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    Exists fun S : RawCompressionStep N (r - s - 1) =>
      S.IsValid /\
        S.before = Gbefore.padRight hNbefore /\
          S.after = Gafter.padRight hNafter /\
            S.cost =
              ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
              S.before.HasRankThresholdPacking /\
                S.after.HasRankThresholdPacking := by
  classical
  by_cases hpos :
      0 < ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost
  · rcases
      E.rankThresholdTopChargedSlot_positive_lifts_to_padded_valid_step_with_state_eq
        hE s q hpos with
        ⟨S, hSvalid, hSbefore, hSafter, _hSpath, hScost, hSpackBefore,
          hSpackAfter⟩
    exact ⟨S, hSvalid, hSbefore, hSafter, hScost, hSpackBefore, hSpackAfter⟩
  · have hzero :
        ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost = 0 :=
      Nat.eq_zero_of_not_pos hpos
    exact E.rankThresholdTopChargedSlot_zero_cost_lifts_to_padded_noop_step
      hE s q hzero

/-- Chosen ordinary padded source step for a compacted charged top slot. -/
noncomputable def rankThresholdTopChargedPaddedStep
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    RawCompressionStep (RankThresholdDissection.topRestrictedBudget (n := n) s)
      (r - s - 1) :=
  Classical.choose
    (E.rankThresholdTopChargedSlot_lifts_to_padded_step_with_state_eq hE s q)

/-- Specification of the chosen charged padded source step. -/
theorem rankThresholdTopChargedPaddedStep_spec
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    let i := E.rankThresholdTopChargedSlot hE s q
    let N := RankThresholdDissection.topRestrictedBudget (n := n) s
    let Gbefore :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).before (hE.1 i).1.1 s
    let hNbefore :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).before (hE.1 i).1.1
        ((E.hasRankThresholdPacking_of_isValid hE i).1) s
    let Gafter :=
      RankThresholdDissection.topRestrictedForestFin
        (E.step i).after (hE.1 i).2.1 s
    let hNafter :=
      RankThresholdDissection.topRestrictedForestFin_card_le_budget
        (E.step i).after (hE.1 i).2.1
        ((E.hasRankThresholdPacking_of_isValid hE i).2) s
    let S := E.rankThresholdTopChargedPaddedStep hE s q
    S.IsValid /\
      S.before = Gbefore.padRight hNbefore /\
        S.after = Gafter.padRight hNafter /\
          S.cost =
            ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost /\
            S.before.HasRankThresholdPacking /\
              S.after.HasRankThresholdPacking := by
  simpa [rankThresholdTopChargedPaddedStep] using
    Classical.choose_spec
      (E.rankThresholdTopChargedSlot_lifts_to_padded_step_with_state_eq hE s q)

/-- Ordinary padded execution obtained by keeping the charged top slots. -/
noncomputable def rankThresholdTopChargedPaddedExecution
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    RawCompressionExecution
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)
      (RankThresholdDissection.topRestrictedBudget (n := n) s)
      (r - s - 1) where
  step := fun q => E.rankThresholdTopChargedPaddedStep hE s q

/-- All chosen charged padded slots are valid ordinary source steps. -/
theorem rankThresholdTopChargedPaddedExecution_hasValidSteps
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).HasValidSteps := by
  intro q
  exact (E.rankThresholdTopChargedPaddedStep_spec hE s q).1

/-- The charged padded execution has rank-threshold packing on every endpoint. -/
theorem rankThresholdTopChargedPaddedExecution_hasRankThresholdPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).HasRankThresholdPacking := by
  intro q
  have hspec := E.rankThresholdTopChargedPaddedStep_spec hE s q
  exact ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩

/-- Consecutive chosen charged padded slots agree as literal forests. -/
theorem rankThresholdTopChargedPaddedExecution_hasConsecutiveStates
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).HasConsecutiveStates := by
  intro q q' hqq'
  have hq := E.rankThresholdTopChargedPaddedStep_spec hE s q
  have hq' := E.rankThresholdTopChargedPaddedStep_spec hE s q'
  have halign :=
    E.rankThresholdTopChargedSlot_padded_after_eq_next_before hE s hqq'
  calc
    ((E.rankThresholdTopChargedPaddedExecution hE s).step q).after =
        (RankThresholdDissection.topRestrictedForestFin
          (E.step (E.rankThresholdTopChargedSlot hE s q)).after
          (hE.1 (E.rankThresholdTopChargedSlot hE s q)).2.1 s).padRight
          (RankThresholdDissection.topRestrictedForestFin_card_le_budget
            (E.step (E.rankThresholdTopChargedSlot hE s q)).after
            (hE.1 (E.rankThresholdTopChargedSlot hE s q)).2.1
            ((E.hasRankThresholdPacking_of_isValid hE
              (E.rankThresholdTopChargedSlot hE s q)).2) s) := by
          simpa [rankThresholdTopChargedPaddedExecution] using hq.2.2.1
    _ =
        (RankThresholdDissection.topRestrictedForestFin
          (E.step (E.rankThresholdTopChargedSlot hE s q')).before
          (hE.1 (E.rankThresholdTopChargedSlot hE s q')).1.1 s).padRight
          (RankThresholdDissection.topRestrictedForestFin_card_le_budget
            (E.step (E.rankThresholdTopChargedSlot hE s q')).before
            (hE.1 (E.rankThresholdTopChargedSlot hE s q')).1.1
            ((E.hasRankThresholdPacking_of_isValid hE
              (E.rankThresholdTopChargedSlot hE s q')).1) s) := by
          simpa using halign
    _ = ((E.rankThresholdTopChargedPaddedExecution hE s).step q').before := by
          simpa [rankThresholdTopChargedPaddedExecution] using hq'.2.1.symm

/-- The charged padded execution is semantically valid. -/
theorem rankThresholdTopChargedPaddedExecution_isSemanticallyValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).IsSemanticallyValid :=
  ⟨E.rankThresholdTopChargedPaddedExecution_hasValidSteps hE s,
    E.rankThresholdTopChargedPaddedExecution_hasConsecutiveStates hE s⟩

/-- The charged padded execution satisfies the legacy base-charge injection. -/
theorem rankThresholdTopChargedPaddedExecution_hasLegacyBaseRankAccounting
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).HasLegacyBaseRankAccounting := by
  exact
    (E.rankThresholdTopChargedPaddedExecution hE s)
      |>.hasLegacyBaseRankAccounting_of_semanticallyValid
        (E.rankThresholdTopChargedPaddedExecution_isSemanticallyValid hE s)

/-- The charged padded execution has the full base/rank accounting certificate. -/
theorem rankThresholdTopChargedPaddedExecution_hasBaseRankAccounting
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).HasBaseRankAccounting :=
  ⟨E.rankThresholdTopChargedPaddedExecution_hasLegacyBaseRankAccounting hE s,
    E.rankThresholdTopChargedPaddedExecution_hasRankThresholdPacking hE s⟩

/-- The charged padded execution is a fully valid ordinary source execution. -/
theorem rankThresholdTopChargedPaddedExecution_isValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).IsValid :=
  (E.rankThresholdTopChargedPaddedExecution hE s).isValid_of_semantic_and_rank
    (E.rankThresholdTopChargedPaddedExecution_isSemanticallyValid hE s)
    (E.rankThresholdTopChargedPaddedExecution_hasBaseRankAccounting hE s)

/-- Cost of a chosen charged padded slot matches the projected charged slot. -/
theorem rankThresholdTopChargedPaddedExecution_step_cost_eq
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (q : Fin
      ((E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount)) :
    ((E.rankThresholdTopChargedPaddedExecution hE s).step q).cost =
      ((E.rankThresholdTopChargedProjectedExecution hE s).step q).cost := by
  exact (E.rankThresholdTopChargedPaddedStep_spec hE s q).2.2.2.1

/-- The ordinary charged padded execution has exactly the top consumable cost. -/
theorem rankThresholdTopChargedPaddedExecution_cost_eq_consumableCost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.rankThresholdTopChargedPaddedExecution hE s).cost =
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
  classical
  let Etop := E.rankThresholdTopChargedPaddedExecution hE s
  let Ct := E.rankThresholdTopChargedProjectedExecution hE s
  calc
    Etop.cost = Etop.stepCostSum := Etop.cost_eq_stepCostSum
    _ = Ct.cost := by
      unfold stepCostSum RawCompressionPath.ProjectedCompressionExecution.cost
      apply Finset.sum_congr rfl
      intro q _hq
      simpa [Etop, Ct] using
        E.rankThresholdTopChargedPaddedExecution_step_cost_eq hE s q
    _ =
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost := by
      simpa [Ct] using
        E.rankThresholdTopChargedProjectedExecution_cost_eq_consumableCost hE s

/-- Top consumable cost is dominated by the assembled padded execution cost. -/
theorem rankThresholdTopProjectedExecution_consumableCost_le_paddedChargedExecution_cost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
      (E.rankThresholdTopChargedPaddedExecution hE s).cost := by
  rw [E.rankThresholdTopChargedPaddedExecution_cost_eq_consumableCost hE s]

/-- The assembled charged padded execution consumes the top side by `topDownCost`. -/
theorem rankThresholdTopProjectedExecution_consumableCost_le_topDownCost_topBudget
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    Ct.consumableCost <=
      topDownCost Ct.chargedCount
        (RankThresholdDissection.topRestrictedBudget (n := n) s)
        (r - s - 1) := by
  classical
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Etop := E.rankThresholdTopChargedPaddedExecution hE s
  have hcost_eq :
      Etop.cost = Ct.consumableCost := by
    simpa [Etop, Ct] using
      E.rankThresholdTopChargedPaddedExecution_cost_eq_consumableCost hE s
  have htop :
      Etop.cost <=
        topDownCost Ct.chargedCount
          (RankThresholdDissection.topRestrictedBudget (n := n) s)
          (r - s - 1) := by
    simpa [Etop, Ct] using
      Etop.cost_le_topDownCost
        (E.rankThresholdTopChargedPaddedExecution_isValid hE s)
  simpa [hcost_eq] using htop

/-- Empty rank-threshold top side forces zero top consumable cost. -/
theorem rankThresholdTopProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hcard : (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card = 0) :
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost = 0 := by
  exact E.canonicalTopProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
    hE.1 (E.rankThresholdDissectionFamily hE.1 s) i0
    (fun i => E.rankThresholdDissectionFamily_topFinset_eq_of_slot
      hE.1 hE.2.1 s i0 i)
    hcard

/-- Positive rank-threshold top consumable cost forces a nonempty stable top side. -/
theorem rankThresholdTopProjectedExecution_topFinset_card_pos_of_consumableCost_pos
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hcost :
      0 <
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost) :
    1 <= (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card := by
  by_contra hnot
  have hcard : (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hzero :=
    E.rankThresholdTopProjectedExecution_consumableCost_eq_zero_of_topFinset_card_eq_zero
      hE s i0 hcard
  omega

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

/-- The number of finite indices `q` with `q + 1 < cut` is `cut - 1`. -/
theorem bottomPrefixEdgeIndexSubtype_card
    (N cut : Nat)
    (hcut : cut <= N + 1) :
    Fintype.card {q : Fin (N + 1) // q.val + 1 < cut} = cut - 1 := by
  classical
  let e : {q : Fin (N + 1) // q.val + 1 < cut} ≃ Fin (cut - 1) := {
    toFun := fun q => ⟨q.1.val, by omega⟩
    invFun := fun k => by
      have hk : k.val < cut - 1 := k.isLt
      have hkcut : k.val + 1 < cut := by omega
      have hkN : k.val < N + 1 := by omega
      exact ⟨⟨k.val, hkN⟩, hkcut⟩
    left_inv := by
      intro q
      apply Subtype.ext
      apply Fin.ext
      rfl
    right_inv := by
      intro k
      apply Fin.ext
      rfl
  }
  simpa using Fintype.card_congr e

/--
Finite units for the source-relevant bottom exceptional boundary charge in a
rank-threshold execution: a slot together with a lower endpoint of an
exceptional bottom-prefix edge.
-/
noncomputable def rankThresholdSourceRelevantBottomExceptionEdgeUnit
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) : Type :=
  Sigma fun i : Fin m =>
    {q : Fin (n + 1) //
      (E.step i).path.IsNonrootPath (E.step i).before ∧
      Not ((E.step i).bottomProjectedStep
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
      q.val + 1 <
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i}

noncomputable instance rankThresholdSourceRelevantBottomExceptionEdgeUnitFintype
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fintype (E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s) := by
  classical
  unfold rankThresholdSourceRelevantBottomExceptionEdgeUnit
  infer_instance

/-- Slotwise `Nat.card` count of source-relevant bottom exceptional edge units. -/
theorem rankThresholdSourceRelevantBottomExceptionEdgeUnit_slot_natCard
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    Nat.card
      {q : Fin (n + 1) //
        (E.step i).path.IsNonrootPath (E.step i).before ∧
        Not ((E.step i).bottomProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
        q.val + 1 <
          E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} =
      (E.step i).sourceRelevantBottomExceptionalCost
        (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
        (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
        (E.dissectionCut_spec hE.1
          (E.rankThresholdDissectionFamily hE.1 s) i) := by
  classical
  by_cases hcond :
      (E.step i).path.IsNonrootPath (E.step i).before ∧
        Not ((E.step i).bottomProjectedStep
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged
  · have hcut_le_fin :
        E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i <= n + 1 := by
      have hcut_len :
          E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i <=
            (E.step i).path.len.val :=
        (E.dissectionCut_spec hE.1 (E.rankThresholdDissectionFamily hE.1 s) i).1
      have hlen_le : (E.step i).path.len.val <= n + 1 :=
        Nat.le_of_lt_succ (E.step i).path.len.isLt
      exact hcut_len.trans hlen_le
    let e :
        {q : Fin (n + 1) //
          (E.step i).path.IsNonrootPath (E.step i).before ∧
          Not ((E.step i).bottomProjectedStep
            (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
            (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
          q.val + 1 <
            E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} ≃
        {q : Fin (n + 1) //
          q.val + 1 <
            E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} := {
      toFun := fun q => ⟨q.1, q.2.2.2⟩
      invFun := fun q => ⟨q.1, ⟨hcond.1, hcond.2, q.2⟩⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rfl
      right_inv := by
        intro q
        apply Subtype.ext
        rfl
    }
    calc
      Nat.card
          {q : Fin (n + 1) //
            (E.step i).path.IsNonrootPath (E.step i).before ∧
            Not ((E.step i).bottomProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i}
          =
        Nat.card
          {q : Fin (n + 1) //
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} :=
            Nat.card_congr e
      _ =
        Fintype.card
          {q : Fin (n + 1) //
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} := by
            rw [Nat.card_eq_fintype_card]
      _ = E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i - 1 :=
            bottomPrefixEdgeIndexSubtype_card n
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              hcut_le_fin
      _ =
        (E.step i).sourceRelevantBottomExceptionalCost
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i) := by
            symm
            have hsrc :=
              (E.step i).sourceRelevantBottomExceptionalCost_eq_if_nonroot_not_charged
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)
            simpa [hcond] using hsrc
  · have hEmpty :
        IsEmpty
          {q : Fin (n + 1) //
            (E.step i).path.IsNonrootPath (E.step i).before ∧
            Not ((E.step i).bottomProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} := by
      refine ⟨?_⟩
      intro q
      exact hcond ⟨q.2.1, q.2.2.1⟩
    have hcard :
        Nat.card
          {q : Fin (n + 1) //
            (E.step i).path.IsNonrootPath (E.step i).before ∧
            Not ((E.step i).bottomProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} = 0 := by
      letI := hEmpty
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero
    calc
      Nat.card
          {q : Fin (n + 1) //
            (E.step i).path.IsNonrootPath (E.step i).before ∧
            Not ((E.step i).bottomProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i}
          = 0 := hcard
      _ =
        (E.step i).sourceRelevantBottomExceptionalCost
          (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
          (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
          (E.dissectionCut_spec hE.1
            (E.rankThresholdDissectionFamily hE.1 s) i) := by
            symm
            have hsrc :=
              (E.step i).sourceRelevantBottomExceptionalCost_eq_if_nonroot_not_charged
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)
            simpa [hcond] using hsrc

/-- A source-relevant bottom exceptional edge unit maps to its stable bottom vertex. -/
noncomputable def rankThresholdSourceRelevantBottomExceptionEdgeVertex
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s →
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset) := by
  classical
  intro u
  rcases u with ⟨i, q, hq⟩
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  change
    (E.step i).path.IsNonrootPath (E.step i).before ∧
      Not ((E.step i).bottomProjectedStep (Dfam i) (hE.1 i)
        (cut i) (hcut i)).IsCharged ∧
      q.val + 1 < cut i at hq
  refine ⟨(E.step i).path.node q, ?_⟩
  have hq_active : q.val < (E.step i).path.len.val := by
    have hcut_le : cut i <= (E.step i).path.len.val := (hcut i).1
    omega
  have hq_cut : q.val < cut i := by
    omega
  have hbottom_i : (Dfam i).IsBottom ((E.step i).path.node q) :=
    (hcut i).2.1 q hq_active hq_cut
  have hmem_i : (E.step i).path.node q ∈ (Dfam i).bottomFinset := by
    simpa using hbottom_i
  have hstable :
      (Dfam i).bottomFinset = (Dfam i0).bottomFinset := by
    exact E.rankThresholdDissectionFamily_bottomFinset_eq_of_slot
      hE.1 hE.2.1 s i0 i
  simpa [hstable] using hmem_i

/--
The source-relevant bottom exceptional edge units inject into the stable bottom
finset.  This packages the same-step rank strictness and cross-step freshness
lemmas into the finite map needed for the remaining cardinality bridge.
-/
theorem rankThresholdSourceRelevantBottomExceptionEdgeVertex_injective
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    Function.Injective
      (E.rankThresholdSourceRelevantBottomExceptionEdgeVertex hE s i0) := by
  classical
  intro u v huv
  rcases u with ⟨i, qi, hi⟩
  rcases v with ⟨j, qj, hj⟩
  let Dfam := E.rankThresholdDissectionFamily hE.1 s
  let cut := E.dissectionCut hE.1 Dfam
  let hcut := E.dissectionCut_spec hE.1 Dfam
  change
    (E.step i).path.IsNonrootPath (E.step i).before ∧
      Not ((E.step i).bottomProjectedStep (Dfam i) (hE.1 i)
        (cut i) (hcut i)).IsCharged ∧
      qi.val + 1 < cut i at hi
  change
    (E.step j).path.IsNonrootPath (E.step j).before ∧
      Not ((E.step j).bottomProjectedStep (Dfam j) (hE.1 j)
        (cut j) (hcut j)).IsCharged ∧
      qj.val + 1 < cut j at hj
  have hnode :
      (E.step i).path.node qi = (E.step j).path.node qj := by
    exact congrArg Subtype.val huv
  rcases lt_trichotomy i.val j.val with hij | hij_eq | hji
  · exact False.elim
      ((E.rankThreshold_sourceRelevantBottomException_future_bottom_edge_ne
        hE s hij hi.1 hi.2.1 qi qj hi.2.2 hj.2.2) hnode)
  · have hfin : i = j := Fin.ext hij_eq
    subst j
    rcases lt_trichotomy qi.val qj.val with hqij | hqeq | hqji
    · exact False.elim
        ((E.rankThreshold_sourceRelevantBottomException_same_step_bottom_edge_ne
          hE s i hi.1 qi qj hqij hj.2.2) hnode)
    · have hqfin : qi = qj := Fin.ext hqeq
      subst qj
      exact congrArg (fun x => Sigma.mk i x) (Subtype.ext rfl)
    · exact False.elim
        ((E.rankThreshold_sourceRelevantBottomException_same_step_bottom_edge_ne
          hE s i hi.1 qj qi hqji hi.2.2) hnode.symm)
  · exact False.elim
      ((E.rankThreshold_sourceRelevantBottomException_future_bottom_edge_ne
        hE s hji hj.1 hj.2.1 qj qi hj.2.2 hi.2.2) hnode.symm)

/-- Cardinality form of the source-relevant bottom exceptional edge injection. -/
theorem rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    Fintype.card (E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s) <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) := by
  classical
  have hle :=
    Fintype.card_le_of_injective
      (E.rankThresholdSourceRelevantBottomExceptionEdgeVertex hE s i0)
      (E.rankThresholdSourceRelevantBottomExceptionEdgeVertex_injective hE s i0)
  let D0 := E.rankThresholdDissectionFamily hE.1 s i0
  have hcard :
      Fintype.card D0.bottomFinset = D0.bottomFinset.card :=
    Fintype.card_coe D0.bottomFinset
  exact hle.trans_eq hcard

/--
The finite edge-unit model counts exactly the canonical source-relevant bottom
exceptional cost sum for the rank-threshold family.
-/
theorem rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    Fintype.card (E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s) =
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s) := by
  classical
  unfold rankThresholdSourceRelevantBottomExceptionEdgeUnit
  unfold canonicalBottomSourceRelevantExceptionalCostSum
    bottomSourceRelevantExceptionalCostSum
  calc
    Fintype.card
        (Sigma fun i : Fin m =>
          {q : Fin (n + 1) //
            (E.step i).path.IsNonrootPath (E.step i).before ∧
            Not ((E.step i).bottomProjectedStep
              (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
              (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
              (E.dissectionCut_spec hE.1
                (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
            q.val + 1 <
              E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i}) =
        Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
          Fintype.card
            {q : Fin (n + 1) //
              (E.step i).path.IsNonrootPath (E.step i).before ∧
              Not ((E.step i).bottomProjectedStep
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
              q.val + 1 <
                E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i} := by
        exact @Fintype.card_sigma (Fin m)
          (fun i =>
            {q : Fin (n + 1) //
              (E.step i).path.IsNonrootPath (E.step i).before ∧
              Not ((E.step i).bottomProjectedStep
                (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
                (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
                (E.dissectionCut_spec hE.1
                  (E.rankThresholdDissectionFamily hE.1 s) i)).IsCharged ∧
              q.val + 1 <
                E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i}) _ _
    _ = Finset.sum (Finset.univ : Finset (Fin m)) fun i =>
          (E.step i).sourceRelevantBottomExceptionalCost
            (E.rankThresholdDissectionFamily hE.1 s i) (hE.1 i)
            (E.dissectionCut hE.1 (E.rankThresholdDissectionFamily hE.1 s) i)
            (E.dissectionCut_spec hE.1
              (E.rankThresholdDissectionFamily hE.1 s) i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hslot :=
          E.rankThresholdSourceRelevantBottomExceptionEdgeUnit_slot_natCard hE s i
        rw [Nat.card_eq_fintype_card] at hslot
        exact hslot

/--
The rank-threshold source-relevant bottom exceptional sum is paid by the stable
bottom boundary side.
-/
theorem rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s) <=
      ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) := by
  have hcount :=
    E.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_eq_relevant_sum hE s
  have hle :=
    E.rankThresholdSourceRelevantBottomExceptionEdgeUnit_card_le_bottomFinset_card
      hE s i0
  calc
    E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
        = Fintype.card (E.rankThresholdSourceRelevantBottomExceptionEdgeUnit hE s) :=
          hcount.symm
    _ <= ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) := hle

/--
The compacted charged bottom projected execution is exactly the consumable cost
of the full rank-threshold bottom projected execution.  This is the direct
projected-cost split: uncharged bottom slots do not contribute to
`consumableCost`.
-/
theorem rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    (E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).consumableCost =
      (E.rankThresholdBottomChargedProjectedExecution hE s).cost := by
  exact (E.rankThresholdBottomChargedProjectedExecution_cost_eq_consumableCost hE s).symm

/--
Direct projected bottom accounting with source-relevant boundary exceptions:
the charged projected part is the bottom consumable cost, and the existing
edge-unit injection bounds the source-relevant uncharged boundary contribution
by the stable bottom side.  This deliberately avoids constructing an ordinary
boundary-inclusive bottom execution.
-/
theorem rankThresholdBottom_consumable_add_boundary_le_chargedProjected_add_bottomCard
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let X :=
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost + X <=
      (E.rankThresholdBottomChargedProjectedExecution hE s).cost + Bcard := by
  intro Cb X Bcard
  have hcost :
      Cb.consumableCost =
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost := by
    simpa [Cb] using
      E.rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
        hE s
  have hboundary :
      X <= Bcard := by
    simpa [X, Bcard] using
      E.rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
        hE s i0
  calc
    Cb.consumableCost + X <= Cb.consumableCost + Bcard :=
      Nat.add_le_add_left hboundary Cb.consumableCost
    _ = (E.rankThresholdBottomChargedProjectedExecution hE s).cost + Bcard := by
      rw [hcost]

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

/-- Faithful rank-threshold packing supplies top packing at any execution slot. -/
noncomputable def rankThresholdDissectionFamily_topPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    RankThresholdDissection.TopPacking (E.step i).before (hE.1 i).1.1 s := by
  exact RankThresholdDissection.topPacking_of_rankThresholdPacking
    (E.step i).before (hE.1 i).1.1
    ((E.hasRankThresholdPacking_of_isValid hE i).1) s

/--
The concrete shifted top restriction at any slot has rank-threshold packing
against the Seidel--Sharir external top budget.
-/
theorem rankThresholdTopRestrictedForestFin_hasRankThresholdPackingWithBudget
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    (RankThresholdDissection.topRestrictedForestFin
      (E.step i).before (hE.1 i).1.1 s).HasRankThresholdPackingWithBudget
        (RankThresholdDissection.topRestrictedBudget (n := n) s) := by
  exact RankThresholdDissection.topRestrictedForestFin_hasRankThresholdPackingWithBudget
    (E.step i).before (hE.1 i).1.1
    ((E.hasRankThresholdPacking_of_isValid hE i).1) s

/--
Padding the concrete shifted top restriction at any slot into the external top
budget gives an ordinary rank-threshold-packing forest.
-/
theorem rankThresholdTopRestrictedForestFin_padded_hasRankThresholdPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    (RankThresholdDissection.topRestrictedForestFin
      (E.step i).before (hE.1 i).1.1 s).padRight
        (RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i).before (hE.1 i).1.1
          ((E.hasRankThresholdPacking_of_isValid hE i).1) s)
      |>.HasRankThresholdPacking := by
  exact RankThresholdDissection.topRestrictedForestFin_padded_hasRankThresholdPacking
    (E.step i).before (hE.1 i).1.1
    ((E.hasRankThresholdPacking_of_isValid hE i).1) s

/-- The concrete bottom restriction at any slot is rank-valid. -/
theorem rankThresholdBottomRestrictedForestFin_isRankValid
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    (RankThresholdDissection.bottomRestrictedForestFin
      (E.step i).before (hE.1 i).1.1 s).IsRankValid := by
  exact RankThresholdDissection.bottomRestrictedForestFin_isRankValid
    (E.step i).before (hE.1 i).1.1 s

/--
The concrete bottom restriction at any slot has exact ordinary rank-threshold
packing, unlike the top restriction which needs an external budget.
-/
theorem rankThresholdBottomRestrictedForestFin_hasRankThresholdPacking
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i : Fin m) :
    (RankThresholdDissection.bottomRestrictedForestFin
      (E.step i).before (hE.1 i).1.1 s).HasRankThresholdPacking := by
  exact RankThresholdDissection.bottomRestrictedForestFin_hasRankThresholdPacking
    (E.step i).before (hE.1 i).1.1
    ((E.hasRankThresholdPacking_of_isValid hE i).1) s

/--
The direct rank-packing invariant localizes to the bottom side of every
rank-threshold dissection in a faithful execution slot.
-/
theorem rankThresholdDissectionFamily_bottom_highRank_card_mul_pow_le_bottomFinset_card
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s t : Nat)
    (i : Fin m) :
    (((E.rankThresholdDissectionFamily hE.1 s i).bottomFinset.filter
        fun v => t < RawRankedForest.rankNat (E.step i).before v).card) *
        2 ^ (t + 1) <=
      (E.rankThresholdDissectionFamily hE.1 s i).bottomFinset.card := by
  simpa [rankThresholdDissectionFamily] using
    RankThresholdDissection.bottom_highRank_card_mul_pow_le_bottom_card
      (E.step i).before (hE.1 i).1.1
      ((E.hasRankThresholdPacking_of_isValid hE i).1) s t

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

/--
For the logarithmic threshold `s`, the stable top side contributes at most `n`
to the source-shift arithmetic when weighted by the old row `g`.
-/
theorem rankThresholdDissectionFamily_two_mul_top_card_mul_g_le
    (Drow : DiamondInput)
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (hstate : forall i j : Fin m, i.val + 1 = j.val ->
      (E.step i).after = (E.step j).before)
    (s : Nat)
    (i0 i : Fin m)
    (hs : Drow.g r <= 2 ^ s)
    (P : RankThresholdDissection.TopPacking (E.step i0).before (hsteps i0).1.1 s) :
    2 * (E.rankThresholdDissectionFamily hsteps s i).topFinset.card *
        Drow.g (r - s - 1) <= n := by
  have hfinset :
      (E.rankThresholdDissectionFamily hsteps s i).topFinset =
        (E.rankThresholdDissectionFamily hsteps s i0).topFinset :=
    E.rankThresholdDissectionFamily_topFinset_eq_of_slot hsteps hstate s i0 i
  have hpack :
      (E.rankThresholdDissectionFamily hsteps s i0).topFinset.card *
          2 ^ (s + 1) <= n :=
    RankThresholdDissection.top_card_mul_pow_le
      (E.step i0).before (hsteps i0).1.1 s P
  have hg_rank : Drow.g (r - s - 1) <= Drow.g r :=
    Drow.monotone (by omega)
  have hg_pow : Drow.g (r - s - 1) <= 2 ^ s := hg_rank.trans hs
  calc
    2 * (E.rankThresholdDissectionFamily hsteps s i).topFinset.card *
        Drow.g (r - s - 1)
        = 2 * (E.rankThresholdDissectionFamily hsteps s i0).topFinset.card *
            Drow.g (r - s - 1) := by rw [hfinset]
    _ <= 2 * (E.rankThresholdDissectionFamily hsteps s i0).topFinset.card *
          2 ^ s := by
        exact Nat.mul_le_mul_left
          (2 * (E.rankThresholdDissectionFamily hsteps s i0).topFinset.card)
          hg_pow
    _ = (E.rankThresholdDissectionFamily hsteps s i0).topFinset.card *
          2 ^ (s + 1) := by
        rw [Nat.pow_succ]
        ring
    _ <= n := hpack

/--
Budgeted top-side version of the same weighted cardinality bound.  This is the
arithmetic target for padded top restricted realizations.
-/
theorem rankThresholdDissectionFamily_two_mul_topBudget_mul_g_le
    (Drow : DiamondInput)
    (_E : RawCompressionExecution m n r)
    (s : Nat)
    (hs : Drow.g r <= 2 ^ s) :
    2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
        Drow.g (r - s - 1) <= n := by
  have hg_rank : Drow.g (r - s - 1) <= Drow.g r :=
    Drow.monotone (by omega)
  exact RankThresholdDissection.two_mul_topRestrictedBudget_mul_le
    (n := n) s (Drow.g (r - s - 1)) (hg_rank.trans hs)

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

/--
Execution-level source-relevant projected accounting.  The bottom exceptional
term here omits source-rootpath-only projected artifacts.
-/
theorem stepCostSum_le_sourceRelevantProjectedParts
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.stepCostSum <=
      (E.bottomProjectedExecution hsteps D cut hcut).consumableCost +
        E.bottomSourceRelevantExceptionalCostSum hsteps D cut hcut +
        (E.topProjectedExecution hsteps D cut hcut).consumableCost +
          E.topProjectedNonrootCount hsteps D cut hcut := by
  classical
  unfold stepCostSum bottomSourceRelevantExceptionalCostSum topProjectedNonrootCount
  unfold RawCompressionPath.ProjectedCompressionExecution.consumableCost
  let B : Fin m -> Nat := fun i =>
    ((E.step i).bottomProjectedStep (D i) (hsteps i) (cut i) (hcut i)).consumableCost
  let R : Fin m -> Nat := fun i =>
    (E.step i).sourceRelevantBottomExceptionalCost (D i) (hsteps i) (cut i) (hcut i)
  let T : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).consumableCost
  let N : Fin m -> Nat := fun i =>
    ((E.step i).topProjectedStep (D i) (hsteps i) (cut i) (hcut i)).nonrootIndicator
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (E.step i).cost) <=
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + R i + T i + N i) := by
    exact Finset.sum_le_sum (by
      intro i _hi
      change (E.step i).cost <= B i + R i + T i + N i
      exact (E.step i).cost_le_sourceRelevantProjectedParts
        (D i) (hsteps i) (cut i) (hcut i))
  have hsplit :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + R i + T i + N i) =
        Finset.sum (Finset.univ : Finset (Fin m)) B +
          Finset.sum (Finset.univ : Finset (Fin m)) R +
          Finset.sum (Finset.univ : Finset (Fin m)) T +
            Finset.sum (Finset.univ : Finset (Fin m)) N := by
    have hgroup :
        Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + R i + T i + N i) =
          Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (B i + R i) + (T i + N i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      omega
    calc
      Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + R i + T i + N i)
          = Finset.sum (Finset.univ : Finset (Fin m)) (fun i => (B i + R i) + (T i + N i)) :=
              hgroup
      _ = Finset.sum (Finset.univ : Finset (Fin m)) (fun i => B i + R i) +
              Finset.sum (Finset.univ : Finset (Fin m)) (fun i => T i + N i) := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.sum (Finset.univ : Finset (Fin m)) B +
              Finset.sum (Finset.univ : Finset (Fin m)) R) +
            (Finset.sum (Finset.univ : Finset (Fin m)) T +
              Finset.sum (Finset.univ : Finset (Fin m)) N) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = Finset.sum (Finset.univ : Finset (Fin m)) B +
            Finset.sum (Finset.univ : Finset (Fin m)) R +
            Finset.sum (Finset.univ : Finset (Fin m)) T +
              Finset.sum (Finset.univ : Finset (Fin m)) N := by
              omega
  exact le_trans hsum (le_of_eq hsplit)

/-- The source-relevant bottom exceptional sum is bounded by source step cost. -/
theorem bottomSourceRelevantExceptionalCostSum_le_stepCostSum
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.bottomSourceRelevantExceptionalCostSum hsteps D cut hcut <= E.stepCostSum := by
  classical
  unfold bottomSourceRelevantExceptionalCostSum stepCostSum
  exact Finset.sum_le_sum (by
    intro i _hi
    exact (E.step i).sourceRelevantBottomExceptionalCost_le_cost
      (D i) (hsteps i) (cut i) (hcut i))

/-- The source-relevant bottom exceptional sum is bounded by execution cost. -/
theorem bottomSourceRelevantExceptionalCostSum_le_cost
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.bottomSourceRelevantExceptionalCostSum hsteps D cut hcut <= E.cost := by
  rw [E.cost_eq_stepCostSum]
  exact E.bottomSourceRelevantExceptionalCostSum_le_stepCostSum hsteps D cut hcut

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

/--
Source-relevant accounting for first-class projected executions.  The explicit
middle term is the only bottom exceptional cost still relevant to `E.cost`.
-/
theorem cost_le_sourceRelevantProjectedExecutions
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before)
    (cut : Fin m -> Nat)
    (hcut : forall i : Fin m, (E.step i).path.HasDissectionCut (D i) (cut i)) :
    E.cost <=
      (E.bottomProjectedExecution hsteps D cut hcut).consumableCost +
        E.bottomSourceRelevantExceptionalCostSum hsteps D cut hcut +
        (E.topProjectedExecution hsteps D cut hcut).consumableCost +
          (E.topProjectedExecution hsteps D cut hcut).nonrootCount := by
  rw [E.cost_eq_stepCostSum]
  exact E.stepCostSum_le_sourceRelevantProjectedParts hsteps D cut hcut

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

/-- Canonical-cut form of source-relevant projected accounting. -/
theorem cost_le_canonicalSourceRelevantProjectedExecutions
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hsteps D).consumableCost +
        E.canonicalBottomSourceRelevantExceptionalCostSum hsteps D +
        (E.canonicalTopProjectedExecution hsteps D).consumableCost +
          (E.canonicalTopProjectedExecution hsteps D).nonrootCount := by
  exact E.cost_le_sourceRelevantProjectedExecutions hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

/-- Canonical source-relevant bottom exceptional cost is bounded by source cost. -/
theorem canonicalBottomSourceRelevantExceptionalCostSum_le_cost
    (E : RawCompressionExecution m n r)
    (hsteps : forall i : Fin m, (E.step i).IsValid)
    (D : forall i : Fin m, RawDissection (E.step i).before) :
    E.canonicalBottomSourceRelevantExceptionalCostSum hsteps D <= E.cost := by
  exact E.bottomSourceRelevantExceptionalCostSum_le_cost hsteps D
    (E.dissectionCut hsteps D) (E.dissectionCut_spec hsteps D)

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
Rank-threshold source-relevant projected accounting.  This is the direct
accounting theorem up to the still-missing bound on the displayed
source-relevant bottom exceptional sum.
-/
theorem rankThreshold_sourceRelevant_projected_accounting
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
        E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
          (E.rankThresholdDissectionFamily hE.1 s) +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  have hmain :
      E.cost <=
        (E.canonicalBottomProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
            (E.rankThresholdDissectionFamily hE.1 s) +
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).nonrootCount :=
    E.cost_le_canonicalSourceRelevantProjectedExecutions hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  simpa [RawCompressionPath.ProjectedCompressionExecution.chargedCount] using hmain

/--
Conditional rank-threshold source-cost accounting with the boundary term
displayed.  The sole extra hypothesis is the exact source-relevant bottom
exceptional charging theorem still missing from the current model.
-/
theorem rankThreshold_source_cost_le_projected_consumable_add_boundary_of_relevant_bound
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hrel :
      E.canonicalBottomSourceRelevantExceptionalCostSum hE.1
          (E.rankThresholdDissectionFamily hE.1 s) <=
        ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card)) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  have hmain := E.rankThreshold_sourceRelevant_projected_accounting hE s
  omega

/--
Direct rank-threshold source-relevant accounting: source-rootpath-only bottom
projected exceptions have been bypassed, and the remaining source-relevant
bottom exceptions are charged to the stable bottom boundary side.
-/
theorem rankThreshold_source_cost_le_projected_consumable_add_boundary
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount := by
  exact E.rankThreshold_source_cost_le_projected_consumable_add_boundary_of_relevant_bound
    hE s i0
    (E.rankThreshold_sourceRelevantBottomExceptionalCostSum_le_bottomFinset_card
      hE s i0)

/-- Small-row case of a source shift step, where `g r <= 1`. -/
theorem topDownCost_le_shift_target_of_g_small
    (Drow : DiamondInput)
    (k : Nat)
    (hprev : SourceBound topDownCost k Drow.g)
    {m n r : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hsmall : Drow.g r <= 1) :
    topDownCost m n r <= (k + 1) * m + 2 * n * Drow.diamond r := by
  have hbase : topDownCost m n r <= k * m + 2 * n * Drow.g r :=
    hprev hm hn
  have htarget :
      k * m + 2 * n * Drow.g r <= (k + 1) * m + 2 * n * Drow.diamond r := by
    rw [Drow.diamond_eq_small hsmall]
    have hkm : k * m <= (k + 1) * m := by
      exact Nat.mul_le_mul_right m (Nat.le_succ k)
    omega
  exact hbase.trans htarget

/--
Arithmetic consumption of the direct source-relevant accounting theorem.  If the
bottom and top consumable projected costs have already been bounded with the
compacted charged-count parameters, then the rank-threshold dissection gives
the diamond-budget bound for this execution.
-/
theorem rankThreshold_source_cost_le_diamond_budget_of_consumable_bounds
    (Drow : DiamondInput)
    (k : Nat)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hs : Drow.g r <= 2 ^ s)
    (hdiamond : Drow.diamond r = 1 + Drow.diamond s)
    (P : RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 s)
    (hbottom :
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        (k + 1) *
          (E.canonicalBottomProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 * ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
            Drow.diamond s)
    (htop :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        k *
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 * ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
            Drow.g (r - s - 1)) :
    E.cost <= (k + 1) * m + 2 * n * Drow.diamond r := by
  classical
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
  let Tcard := (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card
  let ds := Drow.diamond s
  let gt := Drow.g (r - s - 1)
  have hmain :
      E.cost <= Cb.consumableCost + Ct.consumableCost + Bcard + Ct.chargedCount := by
    simpa [Cb, Ct, Bcard] using
      E.rankThreshold_source_cost_le_projected_consumable_add_boundary hE s i0
  have hbottom' :
      Cb.consumableCost <= (k + 1) * Cb.chargedCount + 2 * Bcard * ds := by
    simpa [Cb, Bcard, ds] using hbottom
  have htop' :
      Ct.consumableCost <= k * Ct.chargedCount + 2 * Tcard * gt := by
    simpa [Ct, Tcard, gt] using htop
  have hcounts :
      Cb.chargedCount + Ct.chargedCount <= E.nonrootCount := by
    simpa [Cb, Ct] using E.rankThreshold_projected_nonroot_count_le hE s
  have hcount_m :
      Cb.chargedCount + Ct.chargedCount <= m :=
    hcounts.trans E.nonrootCount_le_length
  have hcoeff :
      (k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount <=
        (k + 1) * m := by
    calc
      (k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount
          = (k + 1) * (Cb.chargedCount + Ct.chargedCount) := by
              ring
      _ <= (k + 1) * m := Nat.mul_le_mul_left (k + 1) hcount_m
  have hBcard_le : Bcard <= n := by
    simpa [Bcard] using
      (Finset.card_le_univ ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset))
  have htopBudget :
      2 * Tcard * gt <= n := by
    simpa [Tcard, gt] using
      E.rankThresholdDissectionFamily_two_mul_top_card_mul_g_le
        Drow hE.1 hE.2.1 s i0 i0 hs P
  have hbottomDiamond :
      2 * Bcard * ds <= 2 * n * ds := by
    exact Nat.mul_le_mul_right ds (Nat.mul_le_mul_left 2 hBcard_le)
  have hboundary :
      2 * Bcard * ds + Bcard + 2 * Tcard * gt <=
        2 * n * Drow.diamond r := by
    calc
      2 * Bcard * ds + Bcard + 2 * Tcard * gt
          <= 2 * n * ds + n + n := by
              omega
      _ = 2 * n * (1 + ds) := by
              ring
      _ = 2 * n * Drow.diamond r := by
              rw [hdiamond]
  have hcombined :
      E.cost <=
        ((k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount) +
          (2 * Bcard * ds + Bcard + 2 * Tcard * gt) := by
    omega
  calc
    E.cost <=
        ((k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount) +
          (2 * Bcard * ds + Bcard + 2 * Tcard * gt) := hcombined
    _ <= (k + 1) * m + 2 * n * Drow.diamond r :=
          Nat.add_le_add hcoeff hboundary

/--
Budgeted-top variant of the source-shift arithmetic consumer.

This is the arithmetic form needed by a padded top restricted realization:
the top consumable term is paid against
`RankThresholdDissection.topRestrictedBudget (n := n) s` instead of the exact
top cardinality, while the final source-shift target is unchanged.
-/
theorem rankThreshold_source_cost_le_diamond_budget_of_topBudget_consumable_bounds
    (Drow : DiamondInput)
    (k : Nat)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (hs : Drow.g r <= 2 ^ s)
    (hdiamond : Drow.diamond r = 1 + Drow.diamond s)
    (hbottom :
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        (k + 1) *
          (E.canonicalBottomProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 * ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
            Drow.diamond s)
    (htop :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
        k *
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
          2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
            Drow.g (r - s - 1)) :
    E.cost <= (k + 1) * m + 2 * n * Drow.diamond r := by
  classical
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
  let Tbudget := RankThresholdDissection.topRestrictedBudget (n := n) s
  let ds := Drow.diamond s
  let gt := Drow.g (r - s - 1)
  have hmain :
      E.cost <= Cb.consumableCost + Ct.consumableCost + Bcard + Ct.chargedCount := by
    simpa [Cb, Ct, Bcard] using
      E.rankThreshold_source_cost_le_projected_consumable_add_boundary hE s i0
  have hbottom' :
      Cb.consumableCost <= (k + 1) * Cb.chargedCount + 2 * Bcard * ds := by
    simpa [Cb, Bcard, ds] using hbottom
  have htop' :
      Ct.consumableCost <= k * Ct.chargedCount + 2 * Tbudget * gt := by
    simpa [Ct, Tbudget, gt] using htop
  have hcounts :
      Cb.chargedCount + Ct.chargedCount <= E.nonrootCount := by
    simpa [Cb, Ct] using E.rankThreshold_projected_nonroot_count_le hE s
  have hcount_m :
      Cb.chargedCount + Ct.chargedCount <= m :=
    hcounts.trans E.nonrootCount_le_length
  have hcoeff :
      (k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount <=
        (k + 1) * m := by
    calc
      (k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount
          = (k + 1) * (Cb.chargedCount + Ct.chargedCount) := by
              ring
      _ <= (k + 1) * m := Nat.mul_le_mul_left (k + 1) hcount_m
  have hBcard_le : Bcard <= n := by
    simpa [Bcard] using
      (Finset.card_le_univ ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset))
  have htopBudget :
      2 * Tbudget * gt <= n := by
    simpa [Tbudget, gt] using
      E.rankThresholdDissectionFamily_two_mul_topBudget_mul_g_le Drow s hs
  have hbottomDiamond :
      2 * Bcard * ds <= 2 * n * ds := by
    exact Nat.mul_le_mul_right ds (Nat.mul_le_mul_left 2 hBcard_le)
  have hboundary :
      2 * Bcard * ds + Bcard + 2 * Tbudget * gt <=
        2 * n * Drow.diamond r := by
    calc
      2 * Bcard * ds + Bcard + 2 * Tbudget * gt
          <= 2 * n * ds + n + n := by
              omega
      _ = 2 * n * (1 + ds) := by
              ring
      _ = 2 * n * Drow.diamond r := by
              rw [hdiamond]
  have hcombined :
      E.cost <=
        ((k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount) +
          (2 * Bcard * ds + Bcard + 2 * Tbudget * gt) := by
    omega
  calc
    E.cost <=
        ((k + 1) * Cb.chargedCount + k * Ct.chargedCount + Ct.chargedCount) +
          (2 * Bcard * ds + Bcard + 2 * Tbudget * gt) := hcombined
    _ <= (k + 1) * m + 2 * n * Drow.diamond r :=
          Nat.add_le_add hcoeff hboundary

/--
Log-threshold specialization of
`rankThreshold_source_cost_le_diamond_budget_of_consumable_bounds`.
-/
theorem rankThreshold_source_cost_le_diamond_budget_of_log_consumable_bounds
    (Drow : DiamondInput)
    (k : Nat)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (i0 : Fin m)
    (hlarge : 1 < Drow.g r)
    (P : RankThresholdDissection.TopPacking (E.step i0).before
      (hE.1 i0).1.1 (ceilLog2 (Drow.g r)))
    (hbottom :
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 (ceilLog2 (Drow.g r)))).consumableCost <=
        (k + 1) *
          (E.canonicalBottomProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 (ceilLog2 (Drow.g r)))).chargedCount +
          2 *
            ((E.rankThresholdDissectionFamily hE.1
              (ceilLog2 (Drow.g r)) i0).bottomFinset.card) *
            Drow.diamond (ceilLog2 (Drow.g r)))
    (htop :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 (ceilLog2 (Drow.g r)))).consumableCost <=
        k *
          (E.canonicalTopProjectedExecution hE.1
            (E.rankThresholdDissectionFamily hE.1 (ceilLog2 (Drow.g r)))).chargedCount +
          2 *
            ((E.rankThresholdDissectionFamily hE.1
              (ceilLog2 (Drow.g r)) i0).topFinset.card) *
            Drow.g (r - ceilLog2 (Drow.g r) - 1)) :
    E.cost <= (k + 1) * m + 2 * n * Drow.diamond r := by
  exact E.rankThreshold_source_cost_le_diamond_budget_of_consumable_bounds
    Drow k hE (ceilLog2 (Drow.g r)) i0
    (le_two_pow_ceilLog2 (Drow.g r))
    (Drow.diamond_eq_large hlarge)
    P hbottom htop

/--
The exact large-row consumable-cost obligations needed to turn the
rank-threshold source-relevant accounting theorem into a source shift step.

This intentionally packages the remaining proof obligations rather than adding
the shift theorem as a model certificate.
-/
def RankThresholdLogConsumableBounds
    (Drow : DiamondInput)
    (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < Drow.g r),
    let s := ceilLog2 (Drow.g r)
    let i0 : Fin m := ⟨0, by omega⟩
    Exists fun P : RankThresholdDissection.TopPacking (E.step i0).before
        (hE.1 i0).1.1 s =>
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          (k + 1) *
            (E.canonicalBottomProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 *
              ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
              Drow.diamond s
      /\
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          k *
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 *
              ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
              Drow.g (r - s - 1)

/--
Conditional source shift from the exact rank-threshold consumable-cost
obligations.  This discharges the recurrence arithmetic and leaves only the
simulation/packing obligations in `RankThresholdLogConsumableBounds`.
-/
theorem sourceShiftStep_of_rankThreshold_log_consumable_bounds
    (Drow : DiamondInput)
    (k : Nat)
    (hconsume : RankThresholdLogConsumableBounds Drow k) :
    SourceShiftStep topDownCost k Drow := by
  intro hprev m n r hm hn
  apply topDownCost_le_of_forall_valid
  intro E hE
  by_cases hsmall : Drow.g r <= 1
  · exact (E.cost_le_topDownCost hE).trans
      (topDownCost_le_shift_target_of_g_small Drow k hprev hm hn hsmall)
  · have hlarge : 1 < Drow.g r := Nat.lt_of_not_ge hsmall
    let s := ceilLog2 (Drow.g r)
    let i0 : Fin m := ⟨0, by omega⟩
    rcases hconsume hm hn E hE hlarge with ⟨P, hbottom, htop⟩
    exact E.rankThreshold_source_cost_le_diamond_budget_of_log_consumable_bounds
      Drow k hE i0 hlarge P
      (by simpa [s, i0] using hbottom)
      (by simpa [s, i0] using htop)

/--
Conditional concrete top-down shift step, specialized to the packet `J` row.
-/
theorem topDown_shift_step_of_rankThreshold_log_consumable_bounds
    (k : Nat)
    (hconsume : RankThresholdLogConsumableBounds (JInput k) k) :
    topDownShiftStepTarget k :=
  sourceShiftStep_of_rankThreshold_log_consumable_bounds (JInput k) k hconsume

/--
Concrete `JInput` consumable-cost package for the source shift step.

Unlike `RankThresholdLogConsumableBounds`, this boundary is allowed to use the
previous-row source bound that is already an argument of `SourceShiftStep`.
The conclusion is intentionally the same pair of bottom/top consumable
inequalities consumed by the existing rank-threshold shift arithmetic.
-/
def RankThresholdJInputConsumableBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    Exists fun P : RankThresholdDissection.TopPacking (E.step i0).before
        (hE.1 i0).1.1 s =>
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          (k + 1) *
            (E.canonicalBottomProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 *
              ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
              (JInput k).diamond s
      /\
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          k *
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 *
              ((E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card) *
              (JInput k).g (r - s - 1)

/--
A concrete `JInput` package plus the previous-row source bound yields the old
log-consumable package specialized to `JInput k`.
-/
theorem rankThresholdLogConsumableBounds_of_rankThresholdJInputConsumableBounds
    (k : Nat)
    (hconsume : RankThresholdJInputConsumableBounds k)
    (hprev : SourceBound topDownCost k (JInput k).g) :
    RankThresholdLogConsumableBounds (JInput k) k := by
  intro m n r hm hn E hE hlarge
  exact hconsume hm hn hprev E hE hlarge

/--
Concrete repaired package boundary for the shift step: if the J-specific
consumable simulation can be proved using the previous-row source bound, the
already-proved rank-threshold arithmetic gives the unchanged shift target.
-/
theorem topDown_shift_step_of_rankThresholdJInputConsumableBounds
    (k : Nat)
    (hconsume : RankThresholdJInputConsumableBounds k) :
    topDownShiftStepTarget k := by
  intro hprev
  exact
    (topDown_shift_step_of_rankThreshold_log_consumable_bounds k
      (rankThresholdLogConsumableBounds_of_rankThresholdJInputConsumableBounds
        k hconsume hprev)) hprev

/--
Smaller concrete recurrence-consumption boundary for `JInput`.

The bottom side is already stated in the successor-row budget needed by the
source-shift arithmetic.  The top side is stated as domination by the previous
row's concrete `topDownCost`; the bridge below consumes it using the
`SourceShiftStep` hypothesis `hprev`, with explicit zero-case guards.
-/
def RankThresholdJInputRecurrenceConsumptionBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    let Tcard := (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card
    Cb.consumableCost <=
        (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s
      /\
      Ct.consumableCost <= topDownCost Ct.chargedCount Tcard (r - s - 1)

/--
Budgeted top recurrence consumption converts to the concrete `JInput` top
consumable field with the external padded top budget.

The only missing premise is the source-realization theorem bounding
`Ct.consumableCost` by `topDownCost` at the padded top budget.
-/
theorem rankThreshold_top_consumableCost_le_JInput_topBudget_of_topDownCost
    (k : Nat)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m)
    (htopCost :
      let Ct :=
        E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)
      Ct.consumableCost <=
        topDownCost Ct.chargedCount
          (RankThresholdDissection.topRestrictedBudget (n := n) s)
          (r - s - 1)) :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    Ct.consumableCost <=
      k * Ct.chargedCount +
        2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
          (JInput k).g (r - s - 1) := by
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  by_cases hzero : Ct.consumableCost = 0
  · simpa [Ct, hzero]
  · have hpos : 0 < Ct.consumableCost := Nat.pos_of_ne_zero hzero
    have hcharged_pos : 1 <= Ct.chargedCount :=
      Nat.succ_le_of_lt (Ct.chargedCount_pos_of_consumableCost_pos hpos)
    have htop_pos :
        1 <= (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card := by
      simpa [Ct] using
        E.rankThresholdTopProjectedExecution_topFinset_card_pos_of_consumableCost_pos
          hE s i0 (by simpa [Ct] using hpos)
    have hcard_le_budget :
        (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card <=
          RankThresholdDissection.topRestrictedBudget (n := n) s := by
      simpa [rankThresholdDissectionFamily] using
        RankThresholdDissection.topRestrictedForestFin_card_le_budget
          (E.step i0).before (hE.1 i0).1.1
          ((E.hasRankThresholdPacking_of_isValid hE i0).1) s
    have hbudget_pos :
        1 <= RankThresholdDissection.topRestrictedBudget (n := n) s :=
      htop_pos.trans hcard_le_budget
    have hsource :
        topDownCost Ct.chargedCount
            (RankThresholdDissection.topRestrictedBudget (n := n) s)
            (r - s - 1) <=
          k * Ct.chargedCount +
            2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
              (JInput k).g (r - s - 1) :=
      hprev hcharged_pos hbudget_pos
    exact htopCost.trans hsource

/--
The assembled charged padded top execution supplies the budgeted `JInput`
top-consumable bound directly.
-/
theorem rankThreshold_top_consumableCost_le_JInput_topBudget
    (k : Nat)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    let Ct :=
      E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    Ct.consumableCost <=
      k * Ct.chargedCount +
        2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
          (JInput k).g (r - s - 1) := by
  exact
    E.rankThreshold_top_consumableCost_le_JInput_topBudget_of_topDownCost
      k hprev hE s i0
      (E.rankThresholdTopProjectedExecution_consumableCost_le_topDownCost_topBudget
        hE s)

/--
Bottom consumable field left after the padded-top construction: the top side is
now supplied internally by the charged padded execution, so this is the only
projection-consumption hypothesis needed for the budgeted-top shift bridge.
-/
def RankThresholdJInputBottomConsumableBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    Cb.consumableCost <=
      (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s

/--
Exact remaining charged-bottom projected recurrence boundary.

The direct boundary-accounting route has already identified
`Cb.consumableCost` with this compacted charged projected cost.  Thus this is
the smallest projected-cost theorem still needed for the bottom field, without
constructing an ordinary boundary-inclusive bottom execution and without using
the known-bad charged-only consecutive-state theorem.
-/
def RankThresholdJInputBottomChargedProjectedBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    let Cb :=
      E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)
    let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
    (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
      (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s

/--
The direct projected split reduces the `JInput` bottom consumable field to the
charged-bottom projected recurrence boundary.
-/
theorem rankThresholdJInputBottomConsumableBounds_of_chargedProjectedBounds
    (k : Nat)
    (hcharged : RankThresholdJInputBottomChargedProjectedBounds k) :
    RankThresholdJInputBottomConsumableBounds k := by
  intro m n r hm hn hprev E hE hlarge
  let s := ceilLog2 ((JInput k).g r)
  let i0 : Fin m := ⟨0, by omega⟩
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
  have hcost :
      Cb.consumableCost =
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost := by
    simpa [Cb] using
      E.rankThresholdBottomProjectedExecution_consumableCost_eq_chargedProjectedExecution_cost
        hE s
  have hcharged' :
      (E.rankThresholdBottomChargedProjectedExecution hE s).cost <=
        (k + 1) * Cb.chargedCount + 2 * Bcard * (JInput k).diamond s := by
    simpa [s, i0, Cb, Bcard] using hcharged hm hn hprev E hE hlarge
  calc
    Cb.consumableCost =
        (E.rankThresholdBottomChargedProjectedExecution hE s).cost := hcost
    _ <= (k + 1) * Cb.chargedCount +
        2 * Bcard * (JInput k).diamond s := hcharged'

/--
Budgeted-top concrete `JInput` consumable package.

This has the same bottom field as `RankThresholdJInputConsumableBounds`, but
uses the external padded top budget in the top field.  That is the form
supported by rank-threshold packing without assuming exact-cardinality top
packing.
-/
def RankThresholdJInputTopBudgetConsumableBounds (k : Nat) : Prop :=
  forall {m n r : Nat}
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hprev : SourceBound topDownCost k (JInput k).g)
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (_hlarge : 1 < (JInput k).g r),
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    Exists fun P : RankThresholdDissection.TopPacking (E.step i0).before
        (hE.1 i0).1.1 s =>
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          (k + 1) *
            (E.canonicalBottomProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 *
              ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) *
              (JInput k).diamond s
      /\
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost <=
          k *
            (E.canonicalTopProjectedExecution hE.1
              (E.rankThresholdDissectionFamily hE.1 s)).chargedCount +
            2 * RankThresholdDissection.topRestrictedBudget (n := n) s *
              (JInput k).g (r - s - 1)

/--
The newly assembled padded-top execution discharges the top field of the
budgeted-top package, leaving only the bottom consumable theorem as input.
-/
theorem rankThresholdJInputTopBudgetConsumableBounds_of_bottomConsumableBounds
    (k : Nat)
    (hbottom : RankThresholdJInputBottomConsumableBounds k) :
    RankThresholdJInputTopBudgetConsumableBounds k := by
  intro m n r hm hn hprev E hE hlarge
  let s := ceilLog2 ((JInput k).g r)
  let i0 : Fin m := ⟨0, by omega⟩
  refine ⟨E.rankThresholdDissectionFamily_topPacking hE s i0, ?_, ?_⟩
  · simpa [s, i0] using hbottom hm hn hprev E hE hlarge
  · simpa [s, i0] using
      E.rankThreshold_top_consumableCost_le_JInput_topBudget k hprev hE s i0

/--
Budgeted-top consumable bounds are sufficient for the unchanged concrete
source shift target.
-/
theorem topDown_shift_step_of_rankThresholdJInputTopBudgetConsumableBounds
    (k : Nat)
    (hconsume : RankThresholdJInputTopBudgetConsumableBounds k) :
    topDownShiftStepTarget k := by
  intro hprev m n r hm hn
  apply topDownCost_le_of_forall_valid
  intro E hE
  by_cases hsmall : (JInput k).g r <= 1
  · exact (E.cost_le_topDownCost hE).trans
      (topDownCost_le_shift_target_of_g_small (JInput k) k hprev hm hn hsmall)
  · have hlarge : 1 < (JInput k).g r := Nat.lt_of_not_ge hsmall
    let s := ceilLog2 ((JInput k).g r)
    let i0 : Fin m := ⟨0, by omega⟩
    rcases hconsume hm hn hprev E hE hlarge with ⟨_P, hbottom, htop⟩
    exact E.rankThreshold_source_cost_le_diamond_budget_of_topBudget_consumable_bounds
      (JInput k) k hE s i0
      (by simpa [s] using le_two_pow_ceilLog2 ((JInput k).g r))
      (by simpa [s] using (JInput k).diamond_eq_large hlarge)
      (by simpa [s, i0] using hbottom)
      (by simpa [s, i0] using htop)

/--
After the padded-top assembly, a bottom consumable bound alone is enough to
prove the concrete source shift step.
-/
theorem topDown_shift_step_of_rankThresholdJInputBottomConsumableBounds
    (k : Nat)
    (hbottom : RankThresholdJInputBottomConsumableBounds k) :
    topDownShiftStepTarget k :=
  topDown_shift_step_of_rankThresholdJInputTopBudgetConsumableBounds k
    (rankThresholdJInputTopBudgetConsumableBounds_of_bottomConsumableBounds
      k hbottom)

/--
The charged-bottom projected recurrence boundary is now the only remaining
bottom-side input needed by the padded-top source-shift bridge.
-/
theorem topDown_shift_step_of_rankThresholdJInputBottomChargedProjectedBounds
    (k : Nat)
    (hcharged : RankThresholdJInputBottomChargedProjectedBounds k) :
    topDownShiftStepTarget k :=
  topDown_shift_step_of_rankThresholdJInputBottomConsumableBounds k
    (rankThresholdJInputBottomConsumableBounds_of_chargedProjectedBounds
      k hcharged)

/--
The recurrence-consumption package is strong enough to feed the concrete
`JInput` consumable package.
-/
theorem rankThresholdJInputConsumableBounds_of_recurrenceConsumptionBounds
    (k : Nat)
    (hconsume : RankThresholdJInputRecurrenceConsumptionBounds k) :
    RankThresholdJInputConsumableBounds k := by
  intro m n r hm hn hprev E hE hlarge
  let s := ceilLog2 ((JInput k).g r)
  let i0 : Fin m := ⟨0, by omega⟩
  let Cb :=
    E.canonicalBottomProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Ct :=
    E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)
  let Bcard := (E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card
  let Tcard := (E.rankThresholdDissectionFamily hE.1 s i0).topFinset.card
  rcases hconsume hm hn hprev E hE hlarge with ⟨hbottom, htopCost⟩
  refine ⟨E.rankThresholdDissectionFamily_topPacking hE s i0, ?_, ?_⟩
  · simpa [s, i0, Cb, Bcard] using hbottom
  · by_cases hzero : Ct.consumableCost = 0
    · have htarget :
          Ct.consumableCost <=
            k * Ct.chargedCount + 2 * Tcard * (JInput k).g (r - s - 1) := by
        omega
      simpa [s, i0, Ct, Tcard] using htarget
    · have hpos : 0 < Ct.consumableCost := Nat.pos_of_ne_zero hzero
      have hcharged_pos : 1 <= Ct.chargedCount :=
        Nat.succ_le_of_lt (Ct.chargedCount_pos_of_consumableCost_pos hpos)
      have htop_pos : 1 <= Tcard := by
        simpa [Tcard] using
          E.rankThresholdTopProjectedExecution_topFinset_card_pos_of_consumableCost_pos
            hE s i0 (by simpa [Ct] using hpos)
      have hsource :
          topDownCost Ct.chargedCount Tcard (r - s - 1) <=
            k * Ct.chargedCount + 2 * Tcard * (JInput k).g (r - s - 1) :=
        hprev hcharged_pos htop_pos
      have htarget :
          Ct.consumableCost <=
            k * Ct.chargedCount + 2 * Tcard * (JInput k).g (r - s - 1) :=
        htopCost.trans hsource
      simpa [s, i0, Ct, Tcard] using htarget

/--
Concrete shift bridge from the smaller recurrence-consumption boundary.
-/
theorem topDown_shift_step_of_rankThresholdJInputRecurrenceConsumptionBounds
    (k : Nat)
    (hconsume : RankThresholdJInputRecurrenceConsumptionBounds k) :
    topDownShiftStepTarget k :=
  topDown_shift_step_of_rankThresholdJInputConsumableBounds k
    (rankThresholdJInputConsumableBounds_of_recurrenceConsumptionBounds k hconsume)

/-- A delayed test row used to audit over-general `DiamondInput` packages. -/
def delayedSubThree (r : Nat) : Nat :=
  r - 3

/--
`r ↦ r - 3` is a valid `DiamondInput`, but it is not one of the concrete `J`
rows.  It is useful for checking which source-shift packages genuinely hold for
all diamond inputs and which only make sense for the concrete hierarchy.
-/
def delayedSubThreeInput : DiamondInput where
  g := delayedSubThree
  zero_eq := by
    simp [delayedSubThree]
  monotone := by
    intro r s hrs
    exact Nat.sub_le_sub_right hrs 3
  unbounded := by
    intro t
    refine ⟨t + 3, ?_⟩
    simp [delayedSubThree]
  lt_self_pos := by
    intro r hr
    unfold delayedSubThree
    omega

@[simp]
theorem delayedSubThreeInput_g_six :
    delayedSubThreeInput.g 6 = 3 := by
  rfl

@[simp]
theorem ceilLog2_delayedSubThreeInput_g_six :
    ceilLog2 (delayedSubThreeInput.g 6) = 2 := by
  native_decide

/--
For the delayed test row, the package's residual top row vanishes at the first
rank where a nontrivial top projected path can exist.
-/
theorem delayedSubThreeInput_g_top_residual_six :
    delayedSubThreeInput.g
      (6 - ceilLog2 (delayedSubThreeInput.g 6) - 1) = 0 := by
  native_decide

/-- First vertex of the faithful delayed-row audit witness. -/
def delayedAuditV0 : Fin 32 := ⟨0, by norm_num⟩

/-- Middle vertex of the faithful delayed-row audit witness. -/
def delayedAuditV1 : Fin 32 := ⟨1, by norm_num⟩

/-- Top parent vertex of the faithful delayed-row audit witness. -/
def delayedAuditV2 : Fin 32 := ⟨2, by norm_num⟩

/-- A rank-packed three-node chain inside a 32-vertex ambient forest. -/
def delayedAuditBefore : RawRankedForest 32 6 where
  parent := fun v =>
    if v.val = 0 then delayedAuditV1 else if v.val = 1 then delayedAuditV2 else v
  rank := fun v =>
    if v.val = 0 then ⟨3, by norm_num⟩
    else if v.val = 1 then ⟨4, by norm_num⟩
    else if v.val = 2 then ⟨5, by norm_num⟩
    else ⟨0, by norm_num⟩

/-- The two-slot path through the first edge of the delayed audit chain. -/
def delayedAuditPath : RawCompressionPath 32 where
  len := ⟨2, by norm_num⟩
  node := fun i => if i.val = 0 then delayedAuditV0 else delayedAuditV1
  target := delayedAuditV1

/-- The forest after compressing `delayedAuditV0` to the old parent of the target. -/
def delayedAuditAfter : RawRankedForest 32 6 where
  parent := fun v =>
    if v.val = 0 then delayedAuditV2 else if v.val = 1 then delayedAuditV2 else v
  rank := delayedAuditBefore.rank

/-- The faithful delayed-row audit step. -/
def delayedAuditStep : RawCompressionStep 32 6 where
  before := delayedAuditBefore
  after := delayedAuditAfter
  path := delayedAuditPath

/-- The delayed audit step is a valid concrete compression step. -/
theorem delayedAuditStep_isValid : delayedAuditStep.IsValid := by
  classical
  refine ⟨?hpath, ?hafterRank, ?hrank, ?hroot, ?hnonroot, ?hunchanged⟩
  · refine ⟨?hrankValid, ?hlen, ?hchain, ?hlast⟩
    · intro v hv
      by_cases h0 : v.val = 0
      · have hv0 : v = delayedAuditV0 := by
          apply Fin.ext
          simpa [delayedAuditV0] using h0
        subst v
        norm_num [delayedAuditStep, delayedAuditBefore, delayedAuditV0,
          delayedAuditV1, delayedAuditV2, RawRankedForest.rankNat]
      · by_cases h1 : v.val = 1
        · have hv1 : v = delayedAuditV1 := by
            apply Fin.ext
            simpa [delayedAuditV1] using h1
          subst v
          norm_num [delayedAuditStep, delayedAuditBefore, delayedAuditV0,
            delayedAuditV1, delayedAuditV2, RawRankedForest.rankNat]
        · exfalso
          apply hv
          change delayedAuditBefore.parent v = v
          have hvzero : v ≠ (0 : Fin 32) := by
            intro hvz
            apply h0
            simpa using congrArg Fin.val hvz
          simp [delayedAuditBefore, hvzero, h1]
    · norm_num [delayedAuditStep, delayedAuditPath]
    · intro i j hij hj
      have hi0 : i.val = 0 := by
        have hlen : delayedAuditStep.path.len.val = 2 := by
          rfl
        omega
      have hj1 : j.val = 1 := by
        omega
      have hi_eq : i = ⟨0, by norm_num⟩ := Fin.ext hi0
      have hj_eq : j = ⟨1, by norm_num⟩ := Fin.ext hj1
      subst i
      subst j
      apply Fin.ext
      norm_num [delayedAuditStep, delayedAuditPath, delayedAuditBefore,
        delayedAuditV0, delayedAuditV1, delayedAuditV2]
    · intro i hi
      have hi1 : i.val = 1 := by
        have hlen : delayedAuditStep.path.len.val = 2 := by
          rfl
        omega
      have hi_eq : i = ⟨1, by norm_num⟩ := Fin.ext hi1
      subst i
      apply Fin.ext
      norm_num [delayedAuditStep, delayedAuditPath, delayedAuditV0,
        delayedAuditV1]
  · intro v hv
    by_cases h0 : v.val = 0
    · have hv0 : v = delayedAuditV0 := by
        apply Fin.ext
        simpa [delayedAuditV0] using h0
      subst v
      norm_num [delayedAuditStep, delayedAuditAfter, delayedAuditBefore,
        delayedAuditV0, delayedAuditV1, delayedAuditV2,
        RawRankedForest.rankNat]
    · by_cases h1 : v.val = 1
      · have hv1 : v = delayedAuditV1 := by
          apply Fin.ext
          simpa [delayedAuditV1] using h1
        subst v
        norm_num [delayedAuditStep, delayedAuditAfter, delayedAuditBefore,
          delayedAuditV0, delayedAuditV1, delayedAuditV2,
          RawRankedForest.rankNat]
      · exfalso
        apply hv
        change delayedAuditAfter.parent v = v
        have hvzero : v ≠ (0 : Fin 32) := by
          intro hvz
          apply h0
          simpa using congrArg Fin.val hvz
        simp [delayedAuditAfter, hvzero, h1]
  · intro v
    rfl
  · intro hroot
    exfalso
    have hnot :
        delayedAuditBefore.parent delayedAuditPath.target ≠ delayedAuditPath.target := by
      norm_num [delayedAuditBefore, delayedAuditPath, delayedAuditV1,
        delayedAuditV2]
    exact hnot hroot
  · intro _hnonroot v hcomp
    rcases hcomp with ⟨i, hi, hnode⟩
    have hi0 : i.val = 0 := by
      have hlen : delayedAuditStep.path.len.val = 2 := by
        rfl
      omega
    have hi_eq : i = ⟨0, by norm_num⟩ := Fin.ext hi0
    subst i
    have hv0 : v = delayedAuditV0 := by
      rw [← hnode]
      apply Fin.ext
      norm_num [delayedAuditStep, delayedAuditPath, delayedAuditV0]
    rw [hv0]
    apply Fin.ext
    norm_num [delayedAuditStep, delayedAuditAfter, delayedAuditBefore,
      delayedAuditPath, delayedAuditV0, delayedAuditV1, delayedAuditV2]
  · intro v hnot
    by_cases h0 : v.val = 0
    · exfalso
      apply hnot
      refine ⟨⟨0, by norm_num⟩, ?_, ?_⟩
      · norm_num [delayedAuditStep, delayedAuditPath]
      · apply Fin.ext
        norm_num [delayedAuditStep, delayedAuditPath, delayedAuditV0, h0]
    · apply Fin.ext
      by_cases h1 : v.val = 1
      · have hv1 : v = delayedAuditV1 := by
          apply Fin.ext
          simpa [delayedAuditV1] using h1
        subst v
        norm_num [delayedAuditStep, delayedAuditAfter, delayedAuditBefore,
          delayedAuditV1, delayedAuditV2]
      · have hvzero : v ≠ (0 : Fin 32) := by
          intro hvz
          apply h0
          simpa using congrArg Fin.val hvz
        norm_num [delayedAuditStep, delayedAuditAfter, delayedAuditBefore,
          delayedAuditV1, delayedAuditV2, hvzero, h1]

/-- All positive-rank vertices in the delayed audit forest lie in the three-node chain. -/
theorem delayedAuditBefore_highRank_card_le_three (s : Nat) :
    (delayedAuditBefore.highRankFinset s).card <= 3 := by
  classical
  let support : Finset (Fin 32) :=
    {delayedAuditV0, delayedAuditV1, delayedAuditV2}
  have hsubset : delayedAuditBefore.highRankFinset s ⊆ support := by
    intro v hv
    have hvhigh : s < delayedAuditBefore.rankNat v := by
      simpa [RawRankedForest.highRankFinset] using hv
    by_cases h0 : v.val = 0
    · have hv0 : v = delayedAuditV0 := by
        apply Fin.ext
        simpa [delayedAuditV0] using h0
      simp [support, hv0]
    · by_cases h1 : v.val = 1
      · have hv1 : v = delayedAuditV1 := by
          apply Fin.ext
          simpa [delayedAuditV1] using h1
        simp [support, hv1]
      · by_cases h2 : v.val = 2
        · have hv2 : v = delayedAuditV2 := by
            apply Fin.ext
            simpa [delayedAuditV2] using h2
          simp [support, hv2]
        · have hrank0 : delayedAuditBefore.rankNat v = 0 := by
            have hvzero : v ≠ (0 : Fin 32) := by
              intro hvz
              apply h0
              simpa using congrArg Fin.val hvz
            simp [delayedAuditBefore, RawRankedForest.rankNat, hvzero, h1, h2]
          omega
  have hcard := Finset.card_le_card hsubset
  have hsupport : support.card = 3 := by
    norm_num [support, delayedAuditV0, delayedAuditV1, delayedAuditV2]
  omega

/-- Above threshold `3`, only the last two chain vertices can remain high-rank. -/
theorem delayedAuditBefore_highRank_card_le_two_of_three_le
    {s : Nat} (hs : 3 <= s) :
    (delayedAuditBefore.highRankFinset s).card <= 2 := by
  classical
  let support : Finset (Fin 32) := {delayedAuditV1, delayedAuditV2}
  have hsubset : delayedAuditBefore.highRankFinset s ⊆ support := by
    intro v hv
    have hvhigh : s < delayedAuditBefore.rankNat v := by
      simpa [RawRankedForest.highRankFinset] using hv
    by_cases h0 : v.val = 0
    · have hrank3 : delayedAuditBefore.rankNat v = 3 := by
        have hv0 : v = delayedAuditV0 := by
          apply Fin.ext
          simpa [delayedAuditV0] using h0
        subst v
        simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0]
      omega
    · by_cases h1 : v.val = 1
      · have hv1 : v = delayedAuditV1 := by
          apply Fin.ext
          simpa [delayedAuditV1] using h1
        simp [support, hv1]
      · by_cases h2 : v.val = 2
        · have hv2 : v = delayedAuditV2 := by
            apply Fin.ext
            simpa [delayedAuditV2] using h2
          simp [support, hv2]
        · have hrank0 : delayedAuditBefore.rankNat v = 0 := by
            have hvzero : v ≠ (0 : Fin 32) := by
              intro hvz
              apply h0
              simpa using congrArg Fin.val hvz
            simp [delayedAuditBefore, RawRankedForest.rankNat, hvzero, h1, h2]
          omega
  have hcard := Finset.card_le_card hsubset
  have hsupport : support.card = 2 := by
    norm_num [support, delayedAuditV1, delayedAuditV2]
  omega

/-- Above threshold `4`, only the rank-five chain vertex can remain high-rank. -/
theorem delayedAuditBefore_highRank_card_le_one_of_four_le
    {s : Nat} (hs : 4 <= s) :
    (delayedAuditBefore.highRankFinset s).card <= 1 := by
  classical
  let support : Finset (Fin 32) := {delayedAuditV2}
  have hsubset : delayedAuditBefore.highRankFinset s ⊆ support := by
    intro v hv
    have hvhigh : s < delayedAuditBefore.rankNat v := by
      simpa [RawRankedForest.highRankFinset] using hv
    by_cases h0 : v.val = 0
    · have hrank3 : delayedAuditBefore.rankNat v = 3 := by
        have hv0 : v = delayedAuditV0 := by
          apply Fin.ext
          simpa [delayedAuditV0] using h0
        subst v
        simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0]
      omega
    · by_cases h1 : v.val = 1
      · have hrank4 : delayedAuditBefore.rankNat v = 4 := by
          have hv1 : v = delayedAuditV1 := by
            apply Fin.ext
            simpa [delayedAuditV1] using h1
          subst v
          simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0,
            delayedAuditV1]
        omega
      · by_cases h2 : v.val = 2
        · have hv2 : v = delayedAuditV2 := by
            apply Fin.ext
            simpa [delayedAuditV2] using h2
          simp [support, hv2]
        · have hrank0 : delayedAuditBefore.rankNat v = 0 := by
            have hvzero : v ≠ (0 : Fin 32) := by
              intro hvz
              apply h0
              simpa using congrArg Fin.val hvz
            simp [delayedAuditBefore, RawRankedForest.rankNat, hvzero, h1, h2]
          omega
  have hcard := Finset.card_le_card hsubset
  have hsupport : support.card = 1 := by
    norm_num [support, delayedAuditV2]
  omega

/-- Above threshold `5`, the delayed audit forest has no high-rank vertices. -/
theorem delayedAuditBefore_highRank_card_eq_zero_of_five_le
    {s : Nat} (hs : 5 <= s) :
    (delayedAuditBefore.highRankFinset s).card = 0 := by
  rw [Finset.card_eq_zero]
  ext v
  constructor
  · intro hv
    have hvhigh : s < delayedAuditBefore.rankNat v := by
      simpa [RawRankedForest.highRankFinset] using hv
    have hrank : delayedAuditBefore.rankNat v <= 5 := by
      by_cases h0 : v.val = 0
      · have hv0 : v = delayedAuditV0 := by
          apply Fin.ext
          simpa [delayedAuditV0] using h0
        subst v
        simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0]
      · by_cases h1 : v.val = 1
        · have hv1 : v = delayedAuditV1 := by
            apply Fin.ext
            simpa [delayedAuditV1] using h1
          subst v
          simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0,
            delayedAuditV1]
        · by_cases h2 : v.val = 2
          · have hv2 : v = delayedAuditV2 := by
              apply Fin.ext
              simpa [delayedAuditV2] using h2
            subst v
            simp [delayedAuditBefore, RawRankedForest.rankNat, delayedAuditV0,
              delayedAuditV1, delayedAuditV2]
          · have hvzero : v ≠ (0 : Fin 32) := by
              intro hvz
              apply h0
              simpa using congrArg Fin.val hvz
            simp [delayedAuditBefore, RawRankedForest.rankNat, hvzero, h1, h2]
    omega
  · intro hv
    simp at hv

/-- The delayed audit before-forest satisfies the repaired rank-packing invariant. -/
theorem delayedAuditBefore_hasRankThresholdPacking :
    delayedAuditBefore.HasRankThresholdPacking := by
  classical
  intro s
  by_cases hs2 : s <= 2
  · interval_cases s
    · have hcard := delayedAuditBefore_highRank_card_le_three 0
      norm_num
      omega
    · have hcard := delayedAuditBefore_highRank_card_le_three 1
      norm_num
      omega
    · have hcard := delayedAuditBefore_highRank_card_le_three 2
      norm_num
      omega
  · have hs3 : 3 <= s := by omega
    by_cases hs4 : s <= 3
    · have hs : s = 3 := by omega
      subst s
      have hcard := delayedAuditBefore_highRank_card_le_two_of_three_le
        (s := 3) (by norm_num)
      norm_num
      omega
    · have hs4le : 4 <= s := by omega
      by_cases hs5 : s <= 4
      · have hs : s = 4 := by omega
        subst s
        have hcard := delayedAuditBefore_highRank_card_le_one_of_four_le
          (s := 4) (by norm_num)
        norm_num
        omega
      · have hs5le : 5 <= s := by omega
        have hzero := delayedAuditBefore_highRank_card_eq_zero_of_five_le
          (s := s) hs5le
        rw [hzero]
        simp

/-- The delayed audit after-forest satisfies the repaired rank-packing invariant. -/
theorem delayedAuditAfter_hasRankThresholdPacking :
    delayedAuditAfter.HasRankThresholdPacking := by
  intro s
  simpa [delayedAuditAfter] using delayedAuditBefore_hasRankThresholdPacking s

/-- One-slot faithful execution built from the delayed audit step. -/
def delayedAuditExecution : RawCompressionExecution 1 32 6 where
  step := fun _ => delayedAuditStep

/-- The delayed audit step has exactly one ordinary source-cost unit. -/
theorem delayedAuditStep_cost :
    delayedAuditStep.cost = 1 := by
  classical
  norm_num [RawCompressionStep.cost, RawCompressionPath.sourceCost,
    RawCompressionPath.cost, RawCompressionPath.IsRootPath, RawRankedForest.IsRoot,
    delayedAuditStep, delayedAuditBefore, delayedAuditPath,
    delayedAuditV1, delayedAuditV2]

/-- The one-slot delayed audit execution is valid in the repaired faithful model. -/
theorem delayedAuditExecution_isValid :
    delayedAuditExecution.IsValid := by
  classical
  refine ⟨?hsteps, ?hstate, ?haccount⟩
  · intro i
    fin_cases i
    exact delayedAuditStep_isValid
  · intro i j hij
    omega
  · refine ⟨?hlegacy, ?hpack⟩
    · let charge :
          delayedAuditExecution.ChargeUnit -> Prod (Fin 32) (Fin (6 - 1)) :=
        fun _ => (delayedAuditV0, ⟨0, by norm_num⟩)
      refine ⟨charge, ?_⟩
      intro a b _h
      rcases a with ⟨i, ai⟩
      rcases b with ⟨j, bj⟩
      fin_cases i
      fin_cases j
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Fin.ext
      have hcost :
          (delayedAuditExecution.step ((fun i => i) ⟨0, by norm_num⟩)).cost = 1 := by
        simpa [delayedAuditExecution] using delayedAuditStep_cost
      have hai : ai.val = 0 := by
        have hlt : ai.val < delayedAuditStep.cost := by
          simpa [delayedAuditExecution] using ai.isLt
        rw [delayedAuditStep_cost] at hlt
        omega
      have hbj : bj.val = 0 := by
        have hlt : bj.val < delayedAuditStep.cost := by
          simpa [delayedAuditExecution] using bj.isLt
        rw [delayedAuditStep_cost] at hlt
        omega
      exact hai.trans hbj.symm
    · intro i
      fin_cases i
      exact ⟨delayedAuditBefore_hasRankThresholdPacking,
        delayedAuditAfter_hasRankThresholdPacking⟩

/-- The canonical rank-threshold cut for the delayed audit execution is the top-only cut. -/
theorem delayedAuditExecution_rankThresholdCut_eq_zero :
    delayedAuditExecution.dissectionCut delayedAuditExecution_isValid.1
      (delayedAuditExecution.rankThresholdDissectionFamily
        delayedAuditExecution_isValid.1 2) ⟨0, by norm_num⟩ = 0 := by
  classical
  let i0 : Fin 1 := ⟨0, by norm_num⟩
  let Dfam :=
    delayedAuditExecution.rankThresholdDissectionFamily
      delayedAuditExecution_isValid.1 2
  let cut := delayedAuditExecution.dissectionCut delayedAuditExecution_isValid.1 Dfam i0
  have hcut :
      (delayedAuditExecution.step i0).path.HasDissectionCut (Dfam i0) cut := by
    simpa [Dfam, cut, i0] using
      delayedAuditExecution.dissectionCut_spec delayedAuditExecution_isValid.1 Dfam i0
  by_contra hne
  have hpos : 0 < cut := Nat.pos_of_ne_zero hne
  have hbottom :
      (Dfam i0).IsBottom ((delayedAuditExecution.step i0).path.node ⟨0, by norm_num⟩) :=
    hcut.2.1 ⟨0, by norm_num⟩
      (by norm_num [delayedAuditExecution, delayedAuditStep, delayedAuditPath, i0])
      hpos
  have htop :
      (Dfam i0).IsTop ((delayedAuditExecution.step i0).path.node ⟨0, by norm_num⟩) := by
    norm_num [Dfam, i0, rankThresholdDissectionFamily,
      RankThresholdDissection.dissection, RankThresholdDissection.topPred,
      RawDissection.IsTop, RawRankedForest.rankNat,
      delayedAuditExecution, delayedAuditStep, delayedAuditBefore,
      delayedAuditPath, delayedAuditV0]
  exact hbottom htop

/--
Local semantic audit for the delayed row: at the same parameters where the
package's residual top row is zero, the concrete step semantics allow a valid
rank-threshold top projection with one consumable edge.
-/
theorem exists_valid_step_with_positive_top_consumable_at_delayed_zero_residual :
    Exists fun S : RawCompressionStep 3 6 =>
      Exists fun hS : S.IsValid =>
        let s := ceilLog2 (delayedSubThreeInput.g 6)
        Exists fun hcut :
            S.path.HasDissectionCut
              (RankThresholdDissection.dissection S.before hS.1.1 s) 0 =>
          (S.topProjectedStep
              (RankThresholdDissection.dissection S.before hS.1.1 s)
              hS 0 hcut).consumableCost = 1 /\
            delayedSubThreeInput.g (6 - s - 1) = 0 := by
  classical
  let v0 : Fin 3 := ⟨0, by norm_num⟩
  let v1 : Fin 3 := ⟨1, by norm_num⟩
  let v2 : Fin 3 := ⟨2, by norm_num⟩
  let F : RawRankedForest 3 6 := {
    parent := fun v =>
      if v.val = 0 then v1 else if v.val = 1 then v2 else v
    rank := fun v =>
      if v.val = 0 then ⟨3, by norm_num⟩
      else if v.val = 1 then ⟨4, by norm_num⟩
      else if v.val = 2 then ⟨5, by norm_num⟩
      else ⟨0, by norm_num⟩
  }
  let P : RawCompressionPath 3 := {
    len := ⟨2, by norm_num⟩
    node := fun i => if i.val = 0 then v0 else v1
    target := v1
  }
  let A : RawRankedForest 3 6 := {
    parent := fun v =>
      if v.val = 0 then v2 else if v.val = 1 then v2 else v
    rank := F.rank
  }
  let S : RawCompressionStep 3 6 := {
    before := F
    after := A
    path := P
  }
  have hS : S.IsValid := by
    refine ⟨?hpath, ?hafterRank, ?hrank, ?hroot, ?hnonroot, ?hunchanged⟩
    · refine ⟨?hrankValid, ?hlen, ?hchain, ?hlast⟩
      · intro v hv
        fin_cases v
        · norm_num [S, F, v0, v1, v2, RawRankedForest.rankNat]
        · norm_num [S, F, v0, v1, v2, RawRankedForest.rankNat]
        · exfalso
          apply hv
          norm_num [S, F, v0, v1, v2]
      · norm_num [S, P]
      · intro i j hij hj
        have hi0 : i.val = 0 := by
          norm_num [S, P] at hj
          omega
        have hj1 : j.val = 1 := by
          omega
        apply Fin.ext
        norm_num [S, P, F, v0, v1, v2, hi0, hj1]
      · intro i hi
        have hi1 : i.val = 1 := by
          norm_num [S, P] at hi
          omega
        apply Fin.ext
        norm_num [S, P, v0, v1, hi1]
    · intro v hv
      fin_cases v
      · norm_num [S, A, F, v0, v1, v2, RawRankedForest.rankNat]
      · norm_num [S, A, F, v0, v1, v2, RawRankedForest.rankNat]
      · exfalso
        apply hv
        norm_num [S, A, F, v0, v1, v2]
    · intro v
      rfl
    · intro hroot
      exfalso
      have hnot : F.parent P.target ≠ P.target := by
        norm_num [F, P, v1, v2]
      exact hnot hroot
    · intro _hnonroot v hcomp
      rcases hcomp with ⟨i, hi, hnode⟩
      have hi0 : i.val = 0 := by
        have hlen : S.path.len.val = 2 := by
          rfl
        omega
      have hv0 : v = v0 := by
        rw [← hnode]
        apply Fin.ext
        norm_num [S, P, v0, hi0]
      rw [hv0]
      apply Fin.ext
      norm_num [S, A, F, P, v0, v1, v2]
    · intro v hnot
      by_cases hv0 : v.val = 0
      · exfalso
        apply hnot
        refine ⟨⟨0, by norm_num⟩, ?_, ?_⟩
        · norm_num [S, P]
        · apply Fin.ext
          norm_num [S, P, v0, hv0]
      · fin_cases v
        · exfalso
          exact hv0 rfl
        · apply Fin.ext
          norm_num [S, A, F]
        · apply Fin.ext
          norm_num [S, A, F]
  let s := ceilLog2 (delayedSubThreeInput.g 6)
  have hs : s = 2 := by
    native_decide
  let D := RankThresholdDissection.dissection S.before hS.1.1 s
  have hcut : S.path.HasDissectionCut D 0 := by
    constructor
    · simp [S, P]
    constructor
    · intro i _hactive hi
      omega
    · intro i hactive _hi
      have hival : i.val = 0 ∨ i.val = 1 := by
        simp [S, P] at hactive
        omega
      rcases hival with hival | hival <;>
        simp [D, s, hs, S, P, F, v0, v1, v2,
          rankThresholdDissectionFamily, RankThresholdDissection.dissection,
          RankThresholdDissection.topPred, RawDissection.IsTop,
          RawRankedForest.rankNat, hival]
  have hcost :
      (S.topProjectedStep D hS 0 hcut).consumableCost = 1 := by
    simp [D, s, hs, S, P, F, A, v0, v1, v2,
      RawCompressionStep.topProjectedStep,
      RawCompressionPath.topProjectionSegment,
      RawCompressionPath.topProjectionLength,
      RawCompressionPath.topProjectionNode,
      RawCompressionPath.topProjectionIndex,
      RawCompressionPath.ProjectedCompressionStep.consumableCost,
      RawCompressionPath.ProjectedCompressionStep.IsCharged,
      RawCompressionPath.ProjectedCompressionStep.IsNonrootPath,
      RawCompressionPath.ProjectedCompressionStep.cost,
      RawCompressionPath.ProjectedPathSegment.edgeCost,
      RawCompressionPath.ProjectedPathSegment.IsNonrootPath,
      RawCompressionPath.ProjectedPathSegment.lastIndex,
      RawDissection.topParent,
      RankThresholdDissection.dissection,
      RankThresholdDissection.topPred,
      RawDissection.IsTop,
      RawRankedForest.rankNat]
    intro h
    cases h
  refine ⟨S, hS, hcut, ?_⟩
  exact ⟨by simpa [D, s] using hcost, by simpa [s, hs] using
    delayedSubThreeInput_g_top_residual_six⟩

/--
The legacy finite skeleton, before rank-threshold packing was added to base
accounting, accepted a one-vertex high-rank root that blocks `TopPacking`.
-/
theorem exists_legacyValidExecution_without_rankThresholdTopPacking_current_model :
    Exists fun E : RawCompressionExecution 1 1 4 =>
      Exists fun hE : E.IsLegacyValidWithoutRankPacking =>
        let i0 : Fin 1 := ⟨0, by omega⟩
        RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 1 ->
          False := by
  classical
  let v0 : Fin 1 := ⟨0, by omega⟩
  let F : RawRankedForest 1 4 := {
    parent := fun _ => v0
    rank := fun _ => ⟨2, by omega⟩
  }
  let P : RawCompressionPath 1 := {
    len := ⟨2, by omega⟩
    node := fun _ => v0
    target := v0
  }
  let S : RawCompressionStep 1 4 := {
    before := F
    after := F
    path := P
  }
  let E : RawCompressionExecution 1 1 4 := {
    step := fun _ => S
  }
  have hS : S.IsValid := by
    refine ⟨?hpath, ?hafterRank, ?hrank, ?hroot, ?hnonroot, ?hunchanged⟩
    · refine ⟨?hrankValid, ?hlen, ?hchain, ?hlast⟩
      · intro v hv
        exfalso
        exact hv (Subsingleton.elim _ _)
      · norm_num [S, P]
      · intro i j hij hj
        exact Subsingleton.elim _ _
      · intro i hi
        exact Subsingleton.elim _ _
    · intro v hv
      exfalso
      exact hv (Subsingleton.elim _ _)
    · intro v
      rfl
    · intro _hroot
      funext v
      exact Subsingleton.elim _ _
    · intro hnonroot
      exact False.elim (hnonroot (Subsingleton.elim _ _))
    · intro v _hv
      exact Subsingleton.elim _ _
  have hE : E.IsLegacyValidWithoutRankPacking := by
    refine ⟨?hsteps, ?hstate, ?haccount⟩
    · intro i
      fin_cases i
      exact hS
    · intro i j hij
      omega
    · have hcost : E.cost = 0 := by
        exact E.cost_eq_zero_of_one_vertex
      have hcard : Fintype.card E.ChargeUnit = 0 := by
        simpa [RawCompressionExecution.cost] using hcost
      haveI : IsEmpty E.ChargeUnit := Fintype.card_eq_zero_iff.mp hcard
      refine ⟨fun q => False.elim (IsEmpty.false q), ?_⟩
      intro q _q' _h
      exact False.elim (IsEmpty.false q)
  let i0 : Fin 1 := ⟨0, by omega⟩
  have hnotPacking :
      RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 1 ->
        False := by
    apply RankThresholdDissection.not_topPacking_of_top_card_mul_pow_gt
    norm_num [E, S, F, i0, v0, RawRankedForest.rankNat, RankThresholdDissection.dissection,
      RankThresholdDissection.topPred, RawDissection.topFinset,
      RawDissection.IsTop]
  exact ⟨E, hE, hnotPacking⟩

/--
The faithful model with rank-threshold packing excludes that old bad witness
shape: every valid execution has the needed top-packing field.
-/
theorem not_exists_validExecution_without_rankThresholdTopPacking_current_model :
    Not (Exists fun E : RawCompressionExecution 1 1 4 =>
      Exists fun hE : E.IsValid =>
        let i0 : Fin 1 := ⟨0, by omega⟩
        RankThresholdDissection.TopPacking (E.step i0).before (hE.1 i0).1.1 1 ->
          False) := by
  classical
  intro hbad
  rcases hbad with
    ⟨E, hE, hnotPacking⟩
  let i0 : Fin 1 := ⟨0, by omega⟩
  exact hnotPacking (E.rankThresholdDissectionFamily_topPacking hE 1 i0)

/--
Length-consumed form of direct rank-threshold source-relevant accounting.
-/
theorem rankThreshold_source_cost_le_projected_consumable_add_boundary_add_length
    (E : RawCompressionExecution m n r)
    (hE : E.IsValid)
    (s : Nat)
    (i0 : Fin m) :
    E.cost <=
      (E.canonicalBottomProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
        (E.canonicalTopProjectedExecution hE.1
          (E.rankThresholdDissectionFamily hE.1 s)).consumableCost +
          ((E.rankThresholdDissectionFamily hE.1 s i0).bottomFinset.card) +
            m := by
  have hmain :=
    E.rankThreshold_source_cost_le_projected_consumable_add_boundary hE s i0
  have hcharge :
      (E.canonicalTopProjectedExecution hE.1
        (E.rankThresholdDissectionFamily hE.1 s)).chargedCount <= m :=
    (E.canonicalTopProjectedExecution hE.1
      (E.rankThresholdDissectionFamily hE.1 s)).chargedCount_le_length
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
