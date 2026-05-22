import PathCompressionDigestion.ConcreteSourceModel

/-!
# Source dissections for the concrete top-down model

This module adds the first concrete dissection layer below
`ConcreteSourceModel`.  It intentionally stops at structural facts: source
dissections, bottom/top restricted parent maps, local path-contiguity, raw
nonrootpath counting, and the rank-threshold dissection bridge.

It does not prove the Seidel--Sharir shift theorem.  In particular, it does not
add a shift certificate to `topDownCost`, `SourceModel`, or any existing
paper-facing theorem.
-/

namespace PathCompressionDigestion

namespace ConcreteSourceModel

open RawRankedForest

/-- The two sides of a source dissection. -/
inductive DissectionSide where
  | bottom
  | top
deriving DecidableEq, Repr

/--
A source dissection of a rooted forest.

The top predicate is upward closed: once a vertex lies in the top part, every
ancestor reached by parent pointers also lies in the top part.  The bottom part
is the complement.
-/
structure RawDissection {n r : Nat} (F : RawRankedForest n r) where
  top : Fin n -> Prop
  upward_closed :
    forall {x a : Fin n}, top x -> F.IsAncestor x a -> top a

namespace RawDissection

variable {n r : Nat} {F : RawRankedForest n r}

/-- Membership in the top side of a dissection. -/
def IsTop (D : RawDissection F) (v : Fin n) : Prop :=
  D.top v

/-- Membership in the bottom side of a dissection. -/
def IsBottom (D : RawDissection F) (v : Fin n) : Prop :=
  Not (D.IsTop v)

/-- Side membership as a predicate on vertices. -/
def sidePred (D : RawDissection F) : DissectionSide -> Fin n -> Prop
  | DissectionSide.bottom => D.IsBottom
  | DissectionSide.top => D.IsTop

/-- The finite set of top vertices. -/
noncomputable def topFinset (D : RawDissection F) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun v => D.IsTop v)

/-- The finite set of bottom vertices. -/
noncomputable def bottomFinset (D : RawDissection F) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun v => D.IsBottom v)

@[simp]
theorem mem_topFinset (D : RawDissection F) (v : Fin n) :
    v ∈ D.topFinset ↔ D.IsTop v := by
  classical
  simp [topFinset, IsTop]

@[simp]
theorem mem_bottomFinset (D : RawDissection F) (v : Fin n) :
    v ∈ D.bottomFinset ↔ D.IsBottom v := by
  classical
  simp [bottomFinset, IsBottom]

theorem bottom_or_top (D : RawDissection F) (v : Fin n) :
    D.IsBottom v \/ D.IsTop v := by
  classical
  by_cases hv : D.IsTop v
  · exact Or.inr hv
  · exact Or.inl hv

theorem not_bottom_and_top (D : RawDissection F) (v : Fin n) :
    Not (D.IsBottom v /\ D.IsTop v) := by
  intro h
  exact h.1 h.2

theorem top_of_ancestor
    (D : RawDissection F)
    {x a : Fin n}
    (hx : D.IsTop x)
    (hxa : F.IsAncestor x a) :
    D.IsTop a :=
  D.upward_closed hx hxa

/-- The parent of a top vertex is top. -/
theorem parent_top
    (D : RawDissection F)
    {v : Fin n}
    (hv : D.IsTop v) :
    D.IsTop (F.parent v) := by
  exact D.top_of_ancestor hv ⟨1, rfl⟩

/-- Contrapositive form used for bottom path prefixes. -/
theorem bottom_of_parent_bottom
    (D : RawDissection F)
    {v : Fin n}
    (hv : D.IsBottom (F.parent v)) :
    D.IsBottom v := by
  intro htop
  exact hv (D.parent_top htop)

/-- Vertices of the top restricted forest. -/
def TopNode (D : RawDissection F) : Type :=
  {v : Fin n // D.IsTop v}

/-- Vertices of the bottom restricted forest. -/
def BottomNode (D : RawDissection F) : Type :=
  {v : Fin n // D.IsBottom v}

/--
Parent map for the top restricted forest.  Upward closure is exactly what makes
this map stay inside the top side.
-/
def topParent (D : RawDissection F) (v : D.TopNode) : D.TopNode :=
  ⟨F.parent v.1, D.parent_top v.2⟩

/--
Parent map for the bottom restricted forest.  A bottom vertex whose original
parent lies in the top side becomes a root of the restricted bottom forest.
-/
noncomputable def bottomParent (D : RawDissection F) (v : D.BottomNode) :
    D.BottomNode := by
  classical
  by_cases hparent : D.IsBottom (F.parent v.1)
  · exact ⟨F.parent v.1, hparent⟩
  · exact ⟨v.1, v.2⟩

@[simp]
theorem topParent_val (D : RawDissection F) (v : D.TopNode) :
    (D.topParent v).1 = F.parent v.1 :=
  rfl

theorem bottomParent_val_of_parent_bottom
    (D : RawDissection F)
    (v : D.BottomNode)
    (hparent : D.IsBottom (F.parent v.1)) :
    (D.bottomParent v).1 = F.parent v.1 := by
  classical
  simp [bottomParent, hparent]

theorem bottomParent_val_of_parent_top
    (D : RawDissection F)
    (v : D.BottomNode)
    (hparent : D.IsTop (F.parent v.1)) :
    (D.bottomParent v).1 = v.1 := by
  classical
  have hnot : Not (D.IsBottom (F.parent v.1)) := by
    intro hb
    exact hb hparent
  simp [bottomParent, hnot]

/-- Rank inherited by a top restricted vertex. -/
def topRankNat (D : RawDissection F) (v : D.TopNode) : Nat :=
  F.rankNat v.1

/-- Rank inherited by a bottom restricted vertex. -/
def bottomRankNat (D : RawDissection F) (v : D.BottomNode) : Nat :=
  F.rankNat v.1

end RawDissection

namespace RawRankedForest

variable {n r : Nat} {F : RawRankedForest n r}

/-- Rank does not decrease along one parent edge in a rank-valid forest. -/
theorem rankNat_le_parent
    (hF : F.IsRankValid)
    (v : Fin n) :
    F.rankNat v <= F.rankNat (F.parent v) := by
  by_cases hroot : F.parent v = v
  · rw [hroot]
  · exact le_of_lt (hF v hroot)

/-- Rank does not decrease along ancestor chains in a rank-valid forest. -/
theorem rankNat_le_parentIter
    (hF : F.IsRankValid)
    (t : Nat)
    (v : Fin n) :
    F.rankNat v <= F.rankNat (F.parentIter t v) := by
  induction t generalizing v with
  | zero =>
      rfl
  | succ t ih =>
      exact (F.rankNat_le_parent hF v).trans (ih (F.parent v))

/-- Iterating one more parent step is the same as parenting the iterated vertex. -/
theorem parentIter_succ_eq_parent_parentIter
    (F : RawRankedForest n r)
    (t : Nat)
    (v : Fin n) :
    F.parentIter (t + 1) v = F.parent (F.parentIter t v) := by
  induction t generalizing v with
  | zero =>
      rfl
  | succ t ih =>
      simpa [parentIter] using ih (F.parent v)

/-- An ancestor relation may be extended by one parent step on the right. -/
theorem isAncestor_parent
    {v a : Fin n}
    (h : F.IsAncestor v a) :
    F.IsAncestor v (F.parent a) := by
  rcases h with ⟨t, ht⟩
  exact ⟨t + 1, by rw [F.parentIter_succ_eq_parent_parentIter, ht]⟩

/-- An ancestor relation may be extended across a known parent edge. -/
theorem isAncestor_of_parent_eq
    {v a b : Fin n}
    (h : F.IsAncestor v a)
    (hparent : F.parent a = b) :
    F.IsAncestor v b := by
  simpa [hparent] using F.isAncestor_parent h

end RawRankedForest

namespace RawCompressionPath

variable {n r : Nat} {F : RawRankedForest n r}

/-- Active path slots. -/
noncomputable def activeFinset (P : RawCompressionPath n) :
    Finset (Fin (n + 1)) := by
  classical
  exact (Finset.univ.filter fun i => i.val < P.len.val)

/-- Active path slots strictly before the target slot. -/
noncomputable def properFinset (P : RawCompressionPath n) :
    Finset (Fin (n + 1)) := by
  classical
  exact (Finset.univ.filter fun i => i.val + 1 < P.len.val)

@[simp]
theorem mem_activeFinset (P : RawCompressionPath n) (i : Fin (n + 1)) :
    i ∈ P.activeFinset ↔ i.val < P.len.val := by
  classical
  simp [activeFinset]

@[simp]
theorem mem_properFinset (P : RawCompressionPath n) (i : Fin (n + 1)) :
    i ∈ P.properFinset ↔ i.val + 1 < P.len.val := by
  classical
  simp [properFinset]

/-- Active slots belonging to one side of a dissection. -/
noncomputable def projectedActiveFinset
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (side : DissectionSide) :
    Finset (Fin (n + 1)) := by
  classical
  exact P.activeFinset.filter fun i => D.sidePred side (P.node i)

/-- Charged non-target slots belonging to one side of a dissection. -/
noncomputable def projectedProperFinset
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (side : DissectionSide) :
    Finset (Fin (n + 1)) := by
  classical
  exact P.properFinset.filter fun i => D.sidePred side (P.node i)

/-- Bottom and top active projections partition the active slots. -/
theorem projectedActive_card_bottom_add_top
    (D : RawDissection F)
    (P : RawCompressionPath n) :
    (P.projectedActiveFinset D DissectionSide.bottom).card +
        (P.projectedActiveFinset D DissectionSide.top).card =
      P.activeFinset.card := by
  classical
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := P.activeFinset)
      (p := fun i : Fin (n + 1) => D.IsTop (P.node i))
  change
    (P.activeFinset.filter (fun i => D.IsBottom (P.node i))).card +
        (P.activeFinset.filter (fun i => D.IsTop (P.node i))).card =
      P.activeFinset.card
  have hbottom :
      P.activeFinset.filter (fun i => D.IsBottom (P.node i)) =
        P.activeFinset.filter (fun i => Not (D.IsTop (P.node i))) := by
    ext i
    simp [RawDissection.IsBottom]
  rw [hbottom]
  rw [Nat.add_comm]
  exact h

/-- Bottom and top charged-slot projections partition the charged slots. -/
theorem projectedProper_card_bottom_add_top
    (D : RawDissection F)
    (P : RawCompressionPath n) :
    (P.projectedProperFinset D DissectionSide.bottom).card +
        (P.projectedProperFinset D DissectionSide.top).card =
      P.properFinset.card := by
  classical
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := P.properFinset)
      (p := fun i : Fin (n + 1) => D.IsTop (P.node i))
  change
    (P.properFinset.filter (fun i => D.IsBottom (P.node i))).card +
        (P.properFinset.filter (fun i => D.IsTop (P.node i))).card =
      P.properFinset.card
  have hbottom :
      P.properFinset.filter (fun i => D.IsBottom (P.node i)) =
        P.properFinset.filter (fun i => Not (D.IsTop (P.node i))) := by
    ext i
    simp [RawDissection.IsBottom]
  rw [hbottom]
  rw [Nat.add_comm]
  exact h

/--
Local path-contiguity: along a valid adjacent parent step, once the path is in
the top side, the next vertex is also in the top side.
-/
theorem top_of_adjacent
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    {i j : Fin (n + 1)}
    (hij : i.val + 1 = j.val)
    (hj : j.val < P.len.val)
    (hi : D.IsTop (P.node i)) :
    D.IsTop (P.node j) := by
  have hparent : F.parent (P.node i) = P.node j := hchain i j hij hj
  exact D.top_of_ancestor hi ⟨1, by simp [RawRankedForest.parentIter, hparent]⟩

/--
Contrapositive local path-contiguity: if the next active vertex is bottom, then
the previous adjacent vertex is bottom.
-/
theorem bottom_of_adjacent
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    {i j : Fin (n + 1)}
    (hij : i.val + 1 = j.val)
    (hj : j.val < P.len.val)
    (hjbottom : D.IsBottom (P.node j)) :
    D.IsBottom (P.node i) := by
  intro hitop
  exact hjbottom (P.top_of_adjacent D hchain hij hj hitop)

/--
Along active path slots, later indices are ancestors of earlier indices.  This
is the global path fact needed to turn local dissection preservation into a
bottom-prefix/top-suffix statement.
-/
theorem ancestor_of_le_active
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    {i j : Fin (n + 1)}
    (hij : i.val <= j.val)
    (hj : j.val < P.len.val) :
    F.IsAncestor (P.node i) (P.node j) := by
  rcases Nat.exists_eq_add_of_le hij with ⟨d, hd⟩
  revert i j
  induction d with
  | zero =>
      intro i j hij hj hd
      have hvals : i.val = j.val := by omega
      have hfin : i = j := Fin.ext hvals
      subst j
      exact ⟨0, rfl⟩
  | succ d ih =>
      intro i j hij hj hd
      let mid : Fin (n + 1) := ⟨i.val + d, by omega⟩
      have hmid_active : mid.val < P.len.val := by
        simp [mid]
        omega
      have hprev : F.IsAncestor (P.node i) (P.node mid) := by
        apply ih
        · simp [mid]
        · exact hmid_active
        · simp [mid]
      have hstep : mid.val + 1 = j.val := by
        simp [mid]
        omega
      have hparent : F.parent (P.node mid) = P.node j :=
        hchain mid j hstep hj
      exact F.isAncestor_of_parent_eq hprev hparent

/-- If an active path slot is top, every later active slot is top. -/
theorem top_suffix_of_le
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    {i j : Fin (n + 1)}
    (hij : i.val <= j.val)
    (hj : j.val < P.len.val)
    (hi : D.IsTop (P.node i)) :
    D.IsTop (P.node j) := by
  exact D.top_of_ancestor hi (P.ancestor_of_le_active hchain hij hj)

/-- If a later active path slot is bottom, every earlier active slot is bottom. -/
theorem bottom_prefix_of_le
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    {i j : Fin (n + 1)}
    (hij : i.val <= j.val)
    (hj : j.val < P.len.val)
    (hjbottom : D.IsBottom (P.node j)) :
    D.IsBottom (P.node i) := by
  intro hitop
  exact hjbottom (P.top_suffix_of_le D hchain hij hj hitop)

/-- Cut predicate for the bottom-prefix/top-suffix split of one raw path. -/
def HasDissectionCut
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat) : Prop :=
  cut <= P.len.val /\
    (forall i : Fin (n + 1),
      i.val < P.len.val -> i.val < cut -> D.IsBottom (P.node i)) /\
    (forall i : Fin (n + 1),
      i.val < P.len.val -> cut <= i.val -> D.IsTop (P.node i))

/--
A dissection cuts every active path into a bottom prefix and a top suffix.  The
cut is the first active top slot, or the active length if no top slot occurs.
-/
theorem exists_dissection_cut
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F) :
    Exists (P.HasDissectionCut D) := by
  classical
  let tops := P.projectedActiveFinset D DissectionSide.top
  by_cases htops : tops.Nonempty
  · let first := tops.min' htops
    have hfirst_mem : first ∈ tops := Finset.min'_mem tops htops
    have hfirst_active : first.val < P.len.val := by
      have hmem_active : first ∈ P.activeFinset := (Finset.mem_filter.mp hfirst_mem).1
      simpa using hmem_active
    have hfirst_top : D.IsTop (P.node first) := by
      have htop_raw := (Finset.mem_filter.mp hfirst_mem).2
      simpa [RawDissection.sidePred] using htop_raw
    refine ⟨first.val, ?_, ?_, ?_⟩
    · exact le_of_lt hfirst_active
    · intro i hia hilt hitop
      have hi_mem : i ∈ tops := by
        simp [tops, projectedActiveFinset, RawDissection.sidePred, hia, hitop]
      have hmin_le : first <= i := Finset.min'_le tops i hi_mem
      have hval_le : first.val <= i.val := hmin_le
      omega
    · intro i hia hcut
      exact P.top_suffix_of_le D hchain hcut hia hfirst_top
  · refine ⟨P.len.val, ?_, ?_, ?_⟩
    · rfl
    · intro i hia _hilt hitop
      have hi_mem : i ∈ tops := by
        simp [tops, projectedActiveFinset, RawDissection.sidePred, hia, hitop]
      exact htops ⟨i, hi_mem⟩
    · intro i hia hcut
      omega

end RawCompressionPath

namespace RawCompressionExecution

variable {m n r : Nat}

/-- Source nonrootpath count for a raw execution. -/
noncomputable def nonrootCount (E : RawCompressionExecution m n r) : Nat := by
  classical
  exact
    ((Finset.univ : Finset (Fin m)).filter fun i =>
      (E.step i).path.IsNonrootPath (E.step i).before).card

theorem nonrootCount_le_length (E : RawCompressionExecution m n r) :
    E.nonrootCount <= m := by
  classical
  unfold nonrootCount
  simpa using
    (Finset.card_filter_le (Finset.univ : Finset (Fin m))
      fun i => (E.step i).path.IsNonrootPath (E.step i).before)

end RawCompressionExecution

namespace RankThresholdDissection

variable {n r : Nat} (F : RawRankedForest n r)

/-- Top side of the rank-threshold dissection: vertices of rank strictly above `s`. -/
def topPred (s : Nat) (v : Fin n) : Prop :=
  s < F.rankNat v

/--
The rank-threshold dissection.  Rank validity makes the strict-above-threshold
side upward closed.
-/
def dissection (hF : F.IsRankValid) (s : Nat) : RawDissection F where
  top := topPred F s
  upward_closed := by
    intro x a hx hxa
    rcases hxa with ⟨t, ht⟩
    have hrank : F.rankNat x <= F.rankNat a := by
      simpa [ht] using F.rankNat_le_parentIter hF t x
    exact lt_of_lt_of_le hx hrank

@[simp]
theorem dissection_isTop
    (hF : F.IsRankValid)
    (s : Nat)
    (v : Fin n) :
    (dissection F hF s).IsTop v ↔ s < F.rankNat v :=
  Iff.rfl

@[simp]
theorem dissection_isBottom
    (hF : F.IsRankValid)
    (s : Nat)
    (v : Fin n) :
    (dissection F hF s).IsBottom v ↔ F.rankNat v <= s := by
  unfold dissection RawDissection.IsBottom RawDissection.IsTop topPred
  omega

/-- The bottom restricted forest has maximum rank at most the threshold `s`. -/
theorem bottom_rank_le
    (hF : F.IsRankValid)
    (s : Nat)
    (v : (dissection F hF s).BottomNode) :
    F.rankNat v.1 <= s := by
  simpa using v.2

/-- Shifted top rank, subtracting the threshold boundary. -/
def topShiftedRank
    (hF : F.IsRankValid)
    (s : Nat)
    (v : (dissection F hF s).TopNode) : Nat :=
  F.rankNat v.1 - (s + 1)

/-- Every raw rank is bounded by the ambient maximum rank parameter. -/
theorem rankNat_le_bound (v : Fin n) :
    F.rankNat v <= r := by
  unfold RawRankedForest.rankNat
  exact Nat.le_of_lt_succ (F.rank v).isLt

/--
The top restricted forest has shifted maximum rank at most `r - s - 1`, the
Nat form of the source `r - s - 1` bound.
-/
theorem top_shifted_rank_le
    (hF : F.IsRankValid)
    (s : Nat)
    (v : (dissection F hF s).TopNode) :
    topShiftedRank F hF s v <= r - s - 1 := by
  unfold topShiftedRank
  have hrank : F.rankNat v.1 <= r := rankNat_le_bound F v.1
  omega

/--
Concrete packing witness for the source rank-forest cardinality fact at a
fixed threshold.  A future worker should derive this packing from the
rank-forest child/subtree property; this structure is only the finite
combinatorial data needed for the cardinality arithmetic below.
-/
structure TopPacking (hF : F.IsRankValid) (s : Nat) where
  pack :
    (dissection F hF s).topFinset -> Fin (2 ^ (s + 1)) -> Fin n
  injective_pack :
    Function.Injective
      (fun p : (dissection F hF s).topFinset × Fin (2 ^ (s + 1)) =>
        pack p.1 p.2)

/-- Nat-friendly multiplicative form of the top-side size bound. -/
theorem top_card_mul_pow_le
    (hF : F.IsRankValid)
    (s : Nat)
    (P : TopPacking F hF s) :
    (dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n := by
  classical
  let T := (dissection F hF s).topFinset
  have hle :
      Fintype.card (T × Fin (2 ^ (s + 1))) <= Fintype.card (Fin n) :=
    Fintype.card_le_of_injective
      (fun p : T × Fin (2 ^ (s + 1)) => P.pack p.1 p.2)
      P.injective_pack
  have hTcard : Fintype.card T = T.card := Fintype.card_coe T
  have hle' : T.card * 2 ^ (s + 1) <= n := by
    simpa [hTcard, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
  simpa [T] using hle'

/-- Divided form of the top-side size bound. -/
theorem top_card_le_div
    (hF : F.IsRankValid)
    (s : Nat)
    (P : TopPacking F hF s) :
    (dissection F hF s).topFinset.card <= n / 2 ^ (s + 1) := by
  have hmul : (dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n :=
    top_card_mul_pow_le F hF s P
  have hpos : 0 < 2 ^ (s + 1) := Nat.pow_pos (by norm_num : 0 < 2)
  exact (Nat.le_div_iff_mul_le hpos).2 hmul

end RankThresholdDissection

end ConcreteSourceModel

end PathCompressionDigestion
