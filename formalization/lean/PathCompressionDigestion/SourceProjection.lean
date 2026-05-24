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
noncomputable def topNodeEquivFin
    (D : RawDissection F) :
    D.TopNode ≃ Fin D.topFinset.card := by
  classical
  exact D.topNodeEquivTopFinset.trans D.topFinset.equivFin

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
