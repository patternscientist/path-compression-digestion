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

/-- Iterating parent pointers from a root stays at that root. -/
theorem parentIter_eq_of_root
    {v : Fin n}
    (hroot : F.parent v = v)
    (t : Nat) :
    F.parentIter t v = v := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      simpa [parentIter, hroot] using ih

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

/--
If a predicate is closed under one parent step, then it is closed under every
iterated parent step.
-/
theorem top_of_parentIter_of_parent_top
    (F : RawRankedForest n r)
    {top : Fin n -> Prop}
    (hparent : forall v : Fin n, top v -> top (F.parent v)) :
    forall t : Nat, forall v : Fin n, top v -> top (F.parentIter t v)
  | 0, _v, hv => hv
  | t + 1, v, hv =>
      top_of_parentIter_of_parent_top F hparent t (F.parent v) (hparent v hv)

end RawRankedForest

namespace RawCompressionPath

variable {n r : Nat} {F : RawRankedForest n r}

/-- A path segment inside a restricted forest with its own parent map. -/
structure ProjectedPathSegment (α : Type*) (parent : α -> α) where
  len : Nat
  node : Fin len -> α
  parent_chain :
    forall {i j : Fin len}, i.val + 1 = j.val -> parent (node i) = node j

namespace ProjectedPathSegment

variable {α : Type*} {parent : α -> α}

/-- Edge-style cost of a projected path segment. -/
def edgeCost (S : ProjectedPathSegment α parent) : Nat :=
  S.len - 1

theorem edgeCost_le_len (S : ProjectedPathSegment α parent) :
    S.edgeCost <= S.len := by
  unfold edgeCost
  omega

end ProjectedPathSegment

/-- A projected one-step object over a restricted vertex type. -/
structure ProjectedCompressionStep (α : Type*) where
  beforeParent : α -> α
  afterParent : α -> α
  path : ProjectedPathSegment α beforeParent

namespace ProjectedCompressionStep

variable {α : Type*}

/-- Path-edge cost of a projected step. -/
def cost (S : ProjectedCompressionStep α) : Nat :=
  S.path.edgeCost

end ProjectedCompressionStep

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

/-- Last active slot of a nonempty raw path. -/
def lastIndex
    (P : RawCompressionPath n)
    (hlen : 1 <= P.len.val) :
    Fin (n + 1) :=
  ⟨P.len.val - 1, by
    have hlen_bound : P.len.val < n + 2 := P.len.isLt
    omega⟩

@[simp]
theorem lastIndex_val
    (P : RawCompressionPath n)
    (hlen : 1 <= P.len.val) :
    (P.lastIndex hlen).val = P.len.val - 1 :=
  rfl

theorem lastIndex_active
    (P : RawCompressionPath n)
    (hlen : 1 <= P.len.val) :
    (P.lastIndex hlen).val < P.len.val := by
  change P.len.val - 1 < P.len.val
  omega

theorem lastIndex_succ
    (P : RawCompressionPath n)
    (hlen : 1 <= P.len.val) :
    (P.lastIndex hlen).val + 1 = P.len.val := by
  simp [lastIndex]
  omega

/--
Every compressed vertex lies below the path target.  This is the source-model
fact needed when a nonroot compression rewires a vertex to the target's old
parent.
-/
theorem target_ancestor_of_compressedVertex
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    {v : Fin n}
    (hcomp : P.IsCompressedVertex v) :
    F.IsAncestor v P.target := by
  rcases hvalid with ⟨_hRank, hlen_two, hchain, hlast⟩
  rcases hcomp with ⟨i, hi_before_target, hnode⟩
  have hlen_one : 1 <= P.len.val := by
    omega
  let j := P.lastIndex hlen_one
  have hj_active : j.val < P.len.val := P.lastIndex_active hlen_one
  have hij : i.val <= j.val := by
    simp [j, lastIndex]
    omega
  have hanc : F.IsAncestor (P.node i) (P.node j) :=
    P.ancestor_of_le_active hchain hij hj_active
  have htarget : P.node j = P.target :=
    hlast j (P.lastIndex_succ hlen_one)
  simpa [hnode, htarget] using hanc

/-- A compressed vertex on a source-nonroot path cannot already be a root. -/
theorem not_root_of_compressedVertex_of_nonroot
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (hnonroot : P.IsNonrootPath F)
    {v : Fin n}
    (hcomp : P.IsCompressedVertex v) :
    Not (F.parent v = v) := by
  intro hroot
  rcases P.target_ancestor_of_compressedVertex hvalid hcomp with ⟨t, ht⟩
  have hv_target : v = P.target := by
    simpa [F.parentIter_eq_of_root hroot t] using ht
  exact hnonroot (by simpa [hv_target] using hroot)

/--
Along a valid source-nonroot path, rank strictly increases from an earlier
active slot to a later active slot.  This supplies same-step distinctness for
charged bottom-prefix edge endpoints.
-/
theorem rankNat_lt_of_lt_active_of_nonroot
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (hnonroot : P.IsNonrootPath F)
    {i j : Fin (n + 1)}
    (hij : i.val < j.val)
    (hj_active : j.val < P.len.val) :
    F.rankNat (P.node i) < F.rankNat (P.node j) := by
  let next : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have hnext_active : next.val < P.len.val := by
    simp [next]
    omega
  have hi_compressed : P.IsCompressedVertex (P.node i) := by
    refine ⟨i, ?_, rfl⟩
    omega
  have hnot_root : Not (F.parent (P.node i) = P.node i) :=
    P.not_root_of_compressedVertex_of_nonroot hvalid hnonroot hi_compressed
  have hparent :
      F.parent (P.node i) = P.node next :=
    hvalid.2.2.1 i next (by simp [next]) hnext_active
  have hrank_next :
      F.rankNat (P.node i) < F.rankNat (P.node next) := by
    simpa [hparent] using hvalid.1 (P.node i) hnot_root
  have hnext_le_j : next.val <= j.val := by
    simp [next]
    omega
  have hancestor :
      F.IsAncestor (P.node next) (P.node j) :=
    P.ancestor_of_le_active hvalid.2.2.1 hnext_le_j hj_active
  rcases hancestor with ⟨t, ht⟩
  have hrank_le :
      F.rankNat (P.node next) <= F.rankNat (P.node j) := by
    simpa [ht] using F.rankNat_le_parentIter hvalid.1 t (P.node next)
  exact lt_of_lt_of_le hrank_next hrank_le

/-- Earlier and later active slots on a valid source-nonroot path have distinct vertices. -/
theorem node_ne_of_lt_active_of_nonroot
    (P : RawCompressionPath n)
    (hvalid : P.IsValidFor F)
    (hnonroot : P.IsNonrootPath F)
    {i j : Fin (n + 1)}
    (hij : i.val < j.val)
    (hj_active : j.val < P.len.val) :
    P.node i ≠ P.node j := by
  intro hsame
  have hlt := P.rankNat_lt_of_lt_active_of_nonroot hvalid hnonroot hij hj_active
  rw [hsame] at hlt
  exact (Nat.lt_irrefl _) hlt

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

/-- The length of the bottom projected path segment associated to a cut. -/
def bottomProjectionLength
    (P : RawCompressionPath n)
    (_D : RawDissection F)
    (cut : Nat)
    (_hcut : P.HasDissectionCut _D cut) : Nat :=
  cut

/-- The length of the top projected path segment associated to a cut. -/
def topProjectionLength
    (P : RawCompressionPath n)
    (_D : RawDissection F)
    (cut : Nat)
    (_hcut : P.HasDissectionCut _D cut) : Nat :=
  P.len.val - cut

theorem bottomProjectionLength_le_len
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.bottomProjectionLength D cut hcut <= P.len.val := by
  simpa [bottomProjectionLength] using hcut.1

theorem topProjectionLength_le_len
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.topProjectionLength D cut hcut <= P.len.val := by
  simp [topProjectionLength]

/-- The bottom and top segment lengths add back to the original active length. -/
theorem projectionLength_add
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.bottomProjectionLength D cut hcut +
        P.topProjectionLength D cut hcut =
      P.len.val := by
  have hcut_len : cut <= P.len.val := hcut.1
  simp [bottomProjectionLength, topProjectionLength]
  omega

/-- Original active slot corresponding to a bottom-projection slot. -/
def bottomProjectionIndex
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    Fin (n + 1) :=
  ⟨i.val, by
    have hlen_le : P.len.val <= n + 1 := Nat.le_of_lt_succ P.len.isLt
    have hcut_len : cut <= P.len.val := hcut.1
    have hi_cut : i.val < cut := by
      simp [bottomProjectionLength] at i
      exact i.isLt
    omega⟩

@[simp]
theorem bottomProjectionIndex_val
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    (P.bottomProjectionIndex D cut hcut i).val = i.val :=
  rfl

/-- Original active slot corresponding to a top-projection slot. -/
def topProjectionIndex
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    Fin (n + 1) :=
  ⟨cut + i.val, by
    have hlen_le : P.len.val <= n + 1 := Nat.le_of_lt_succ P.len.isLt
    have hcut_len : cut <= P.len.val := hcut.1
    have hi_len : i.val < P.len.val - cut := by
      simp [topProjectionLength] at i
      exact i.isLt
    omega⟩

@[simp]
theorem topProjectionIndex_val
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    (P.topProjectionIndex D cut hcut i).val = cut + i.val :=
  rfl

theorem bottomProjectionIndex_lt_cut
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    (P.bottomProjectionIndex D cut hcut i).val < cut := by
  simp [bottomProjectionIndex, bottomProjectionLength]

theorem topProjectionIndex_ge_cut
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    cut <= (P.topProjectionIndex D cut hcut i).val := by
  simp [topProjectionIndex]

theorem bottomProjectionIndex_active
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    (P.bottomProjectionIndex D cut hcut i).val < P.len.val := by
  have hcut_len : cut <= P.len.val := hcut.1
  have hi_cut : i.val < cut := by
    simp [bottomProjectionLength] at i
    exact i.isLt
  simp [bottomProjectionIndex]
  omega

theorem topProjectionIndex_active
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    (P.topProjectionIndex D cut hcut i).val < P.len.val := by
  have hcut_len : cut <= P.len.val := hcut.1
  have hi_len : i.val < P.len.val - cut := by
    simp [topProjectionLength] at i
    exact i.isLt
  simp [topProjectionIndex]
  omega

/-- Vertex of the bottom restricted forest at a bottom-projection slot. -/
def bottomProjectionNode
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    D.BottomNode :=
  ⟨P.node (P.bottomProjectionIndex D cut hcut i),
    hcut.2.1 (P.bottomProjectionIndex D cut hcut i)
      (P.bottomProjectionIndex_active D cut hcut i)
      (by
        simp [bottomProjectionLength] at i
        exact i.isLt)⟩

@[simp]
theorem bottomProjectionNode_val
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.bottomProjectionLength D cut hcut)) :
    (P.bottomProjectionNode D cut hcut i).1 =
      P.node (P.bottomProjectionIndex D cut hcut i) :=
  rfl

/-- Vertex of the top restricted forest at a top-projection slot. -/
def topProjectionNode
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    D.TopNode :=
  ⟨P.node (P.topProjectionIndex D cut hcut i),
    hcut.2.2 (P.topProjectionIndex D cut hcut i)
      (P.topProjectionIndex_active D cut hcut i)
      (by simp [topProjectionIndex])⟩

@[simp]
theorem topProjectionNode_val
    (P : RawCompressionPath n)
    (D : RawDissection F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    (i : Fin (P.topProjectionLength D cut hcut)) :
    (P.topProjectionNode D cut hcut i).1 =
      P.node (P.topProjectionIndex D cut hcut i) :=
  rfl

/--
Adjacent slots in the bottom projection follow the restricted bottom parent
map.
-/
theorem bottomProjection_parent_chain
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    {i j : Fin (P.bottomProjectionLength D cut hcut)}
    (hij : i.val + 1 = j.val) :
    D.bottomParent (P.bottomProjectionNode D cut hcut i) =
      P.bottomProjectionNode D cut hcut j := by
  apply Subtype.ext
  have hj_active :
      (P.bottomProjectionIndex D cut hcut j).val < P.len.val :=
    P.bottomProjectionIndex_active D cut hcut j
  have hstep :
      (P.bottomProjectionIndex D cut hcut i).val + 1 =
        (P.bottomProjectionIndex D cut hcut j).val := by
    simpa using hij
  have hparent :
      F.parent (P.node (P.bottomProjectionIndex D cut hcut i)) =
        P.node (P.bottomProjectionIndex D cut hcut j) :=
    hchain (P.bottomProjectionIndex D cut hcut i)
      (P.bottomProjectionIndex D cut hcut j) hstep hj_active
  have hj_bottom :
      D.IsBottom (P.node (P.bottomProjectionIndex D cut hcut j)) :=
    (P.bottomProjectionNode D cut hcut j).2
  have hparent_bottom :
      D.IsBottom (F.parent (P.node (P.bottomProjectionIndex D cut hcut i))) := by
    simpa [hparent] using hj_bottom
  have hbottom_val :
      (D.bottomParent (P.bottomProjectionNode D cut hcut i)).1 =
        F.parent (P.node (P.bottomProjectionIndex D cut hcut i)) :=
    D.bottomParent_val_of_parent_bottom
      (P.bottomProjectionNode D cut hcut i) hparent_bottom
  exact hbottom_val.trans hparent

/--
Adjacent slots in the top projection follow the restricted top parent map.
-/
theorem topProjection_parent_chain
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut)
    {i j : Fin (P.topProjectionLength D cut hcut)}
    (hij : i.val + 1 = j.val) :
    D.topParent (P.topProjectionNode D cut hcut i) =
      P.topProjectionNode D cut hcut j := by
  apply Subtype.ext
  have hj_active :
      (P.topProjectionIndex D cut hcut j).val < P.len.val :=
    P.topProjectionIndex_active D cut hcut j
  have hstep :
      (P.topProjectionIndex D cut hcut i).val + 1 =
        (P.topProjectionIndex D cut hcut j).val := by
    simp [topProjectionIndex]
    omega
  have hparent :
      F.parent (P.node (P.topProjectionIndex D cut hcut i)) =
        P.node (P.topProjectionIndex D cut hcut j) :=
    hchain (P.topProjectionIndex D cut hcut i)
      (P.topProjectionIndex D cut hcut j) hstep hj_active
  simpa [RawDissection.topParent] using hparent

/-- Packaged bottom projected path segment for a dissection cut. -/
def bottomProjectionSegment
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    ProjectedPathSegment D.BottomNode D.bottomParent where
  len := P.bottomProjectionLength D cut hcut
  node := P.bottomProjectionNode D cut hcut
  parent_chain := by
    intro i j hij
    exact P.bottomProjection_parent_chain D hchain cut hcut hij

@[simp]
theorem bottomProjectionSegment_len
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    (P.bottomProjectionSegment D hchain cut hcut).len =
      P.bottomProjectionLength D cut hcut :=
  rfl

/-- Packaged top projected path segment for a dissection cut. -/
def topProjectionSegment
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    ProjectedPathSegment D.TopNode D.topParent where
  len := P.topProjectionLength D cut hcut
  node := P.topProjectionNode D cut hcut
  parent_chain := by
    intro i j hij
    exact P.topProjection_parent_chain D hchain cut hcut hij

@[simp]
theorem topProjectionSegment_len
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    (P.topProjectionSegment D hchain cut hcut).len =
      P.topProjectionLength D cut hcut :=
  rfl

/--
Path-level cost accounting for a dissection cut: splitting a path into bottom
and top contiguous segments loses at most the one cross-dissection edge.
-/
theorem cost_le_projection_edgeCosts_add_one
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.cost <=
      (P.bottomProjectionSegment D hchain cut hcut).edgeCost +
        (P.topProjectionSegment D hchain cut hcut).edgeCost + 1 := by
  unfold cost ProjectedPathSegment.edgeCost
  have hsum := P.projectionLength_add D cut hcut
  simp [bottomProjectionSegment, topProjectionSegment]
  omega

/-- Source path cost is bounded by the same projected edge-cost accounting. -/
theorem sourceCost_le_projection_edgeCosts_add_one
    (D : RawDissection F)
    (P : RawCompressionPath n)
    (hchain : P.IsParentChain F)
    (cut : Nat)
    (hcut : P.HasDissectionCut D cut) :
    P.sourceCost F <=
      (P.bottomProjectionSegment D hchain cut hcut).edgeCost +
        (P.topProjectionSegment D hchain cut hcut).edgeCost + 1 := by
  classical
  unfold sourceCost
  by_cases hroot : P.IsRootPath F
  · rw [if_pos hroot]
    omega
  · rw [if_neg hroot]
    exact P.cost_le_projection_edgeCosts_add_one D hchain cut hcut

end RawCompressionPath

namespace RawCompressionStep

variable {n r : Nat}

/--
A top vertex remains top after one valid compression step when the same
dissection predicate is read on the after-forest.
-/
theorem after_parent_top
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    {v : Fin n}
    (hv : D.IsTop v) :
    D.IsTop (S.after.parent v) := by
  rcases hS with
    ⟨hpath, _hafterRank, _hrank, hroot_step, hnonroot_step, hunchanged⟩
  by_cases hroot : S.path.IsRootPath S.before
  · have hparent_eq : S.after.parent = S.before.parent := hroot_step hroot
    rw [hparent_eq]
    exact D.parent_top hv
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v
    · have hrewire :
          S.after.parent v = S.before.parent S.path.target :=
        hnonroot_step hnonroot v hcomp
      rw [hrewire]
      have htarget_ancestor : S.before.IsAncestor v S.path.target :=
        S.path.target_ancestor_of_compressedVertex hpath hcomp
      have htarget_top : D.IsTop S.path.target :=
        D.top_of_ancestor hv htarget_ancestor
      exact D.parent_top htarget_top
    · have hsame : S.after.parent v = S.before.parent v :=
        hunchanged v hcomp
      rw [hsame]
      exact D.parent_top hv

/--
If a vertex already has a top parent before a valid compression step, then it
still has a top parent afterwards.  This is the local persistence fact used by
source-relevant boundary charging: once a bottom vertex has crossed to the top
side, later source steps cannot make its parent bottom again.
-/
theorem after_parent_top_of_parent_top
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    {v : Fin n}
    (hv : D.IsTop (S.before.parent v)) :
    D.IsTop (S.after.parent v) := by
  rcases hS with
    ⟨hpath, _hafterRank, _hrank, hroot_step, hnonroot_step, hunchanged⟩
  by_cases hroot : S.path.IsRootPath S.before
  · have hparent_eq : S.after.parent = S.before.parent := hroot_step hroot
    rw [hparent_eq]
    exact hv
  · have hnonroot : S.path.IsNonrootPath S.before := by
      simpa [RawCompressionPath.IsRootPath, RawCompressionPath.IsNonrootPath,
        RawRankedForest.IsRoot] using hroot
    by_cases hcomp : S.path.IsCompressedVertex v
    · have hrewire :
          S.after.parent v = S.before.parent S.path.target :=
        hnonroot_step hnonroot v hcomp
      rw [hrewire]
      have htarget_ancestor : S.before.IsAncestor v S.path.target :=
        S.path.target_ancestor_of_compressedVertex hpath hcomp
      have hparent_target_ancestor :
          S.before.IsAncestor (S.before.parent v) (S.before.parent S.path.target) := by
        rcases htarget_ancestor with ⟨t, ht⟩
        cases t with
        | zero =>
            have hv_target : v = S.path.target := by
              simpa [RawRankedForest.parentIter] using ht
            exact ⟨0, by simp [RawRankedForest.parentIter, hv_target]⟩
        | succ t =>
            have hparent_target : S.before.IsAncestor (S.before.parent v) S.path.target := by
              exact ⟨t, by simpa [RawRankedForest.parentIter] using ht⟩
            exact S.before.isAncestor_parent hparent_target
      exact D.top_of_ancestor hv hparent_target_ancestor
    · have hsame : S.after.parent v = S.before.parent v :=
        hunchanged v hcomp
      rw [hsame]
      exact hv

/--
The same top set is still upward closed after a valid raw compression step.
This is the one-step dissection-preservation bridge needed before projected
steps can be assembled.
-/
def afterDissection
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    RawDissection S.after where
  top := D.top
  upward_closed := by
    intro x a hx hxa
    rcases hxa with ⟨t, ht⟩
    have hiter :
        D.IsTop (S.after.parentIter t x) :=
      S.after.top_of_parentIter_of_parent_top
        (top := D.top)
        (fun v hv => S.after_parent_top D hS hv)
        t x hx
    simpa [RawDissection.IsTop, ht] using hiter

@[simp]
theorem afterDissection_isTop
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : Fin n) :
    (S.afterDissection D hS).IsTop v ↔ D.IsTop v :=
  Iff.rfl

@[simp]
theorem afterDissection_isBottom
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : Fin n) :
    (S.afterDissection D hS).IsBottom v ↔ D.IsBottom v :=
  Iff.rfl

@[simp]
theorem afterDissection_topFinset
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    (S.afterDissection D hS).topFinset = D.topFinset := by
  classical
  ext v
  simp

@[simp]
theorem afterDissection_bottomFinset
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    (S.afterDissection D hS).bottomFinset = D.bottomFinset := by
  classical
  ext v
  simp

theorem afterDissection_top_card
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    (S.afterDissection D hS).topFinset.card = D.topFinset.card := by
  simp

theorem afterDissection_bottom_card
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    (S.afterDissection D hS).bottomFinset.card = D.bottomFinset.card := by
  simp

/-- After-step top parent, represented on the original top-node subtype. -/
def afterTopParent
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.TopNode) :
    D.TopNode :=
  ⟨S.after.parent v.1, S.after_parent_top D hS v.2⟩

@[simp]
theorem afterTopParent_val
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.TopNode) :
    (S.afterTopParent D hS v).1 = S.after.parent v.1 :=
  rfl

/--
After-step bottom parent, represented on the original bottom-node subtype.
As with `RawDissection.bottomParent`, an edge crossing into the top side is
truncated into a restricted-forest root.
-/
noncomputable def afterBottomParent
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (_hS : S.IsValid)
    (v : D.BottomNode) :
    D.BottomNode := by
  classical
  by_cases hparent : D.IsBottom (S.after.parent v.1)
  · exact ⟨S.after.parent v.1, hparent⟩
  · exact ⟨v.1, v.2⟩

theorem afterBottomParent_val_of_parent_bottom
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.BottomNode)
    (hparent : D.IsBottom (S.after.parent v.1)) :
    (S.afterBottomParent D hS v).1 = S.after.parent v.1 := by
  classical
  simp [afterBottomParent, hparent]

theorem afterBottomParent_val_of_parent_top
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (v : D.BottomNode)
    (hparent : D.IsTop (S.after.parent v.1)) :
    (S.afterBottomParent D hS v).1 = v.1 := by
  classical
  have hnot : Not (D.IsBottom (S.after.parent v.1)) := by
    intro hb
    exact hb hparent
  simp [afterBottomParent, hnot]

/-- A valid raw step's path admits a dissection cut. -/
theorem exists_path_dissection_cut
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    Exists (S.path.HasDissectionCut D) := by
  exact S.path.exists_dissection_cut D hS.1.2.2.1

/--
One-step path accounting, packaged at `RawCompressionStep` level.  This is not
yet the projected-step commutation theorem, but it supplies the local cost
inequality that projected executions must sum.
-/
theorem exists_projection_segments_cost_bound
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid) :
    Exists fun cut : Nat =>
      Exists fun hcut : S.path.HasDissectionCut D cut =>
        S.cost <=
          (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost +
            (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost + 1 := by
  rcases S.exists_path_dissection_cut D hS with ⟨cut, hcut⟩
  refine ⟨cut, hcut, ?_⟩
  unfold cost
  exact S.path.sourceCost_le_projection_edgeCosts_add_one D hS.1.2.2.1 cut hcut

/-- Bottom projected step for a fixed dissection cut. -/
noncomputable def bottomProjectedStep
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    RawCompressionPath.ProjectedCompressionStep D.BottomNode where
  beforeParent := D.bottomParent
  afterParent := S.afterBottomParent D hS
  path := S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut

/-- Top projected step for a fixed dissection cut. -/
def topProjectedStep
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    RawCompressionPath.ProjectedCompressionStep D.TopNode where
  beforeParent := D.topParent
  afterParent := S.afterTopParent D hS
  path := S.path.topProjectionSegment D hS.1.2.2.1 cut hcut

@[simp]
theorem bottomProjectedStep_cost
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    (S.bottomProjectedStep D hS cut hcut).cost =
      (S.path.bottomProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost :=
  rfl

@[simp]
theorem topProjectedStep_cost
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    (S.topProjectedStep D hS cut hcut).cost =
      (S.path.topProjectionSegment D hS.1.2.2.1 cut hcut).edgeCost :=
  rfl

/-- One-step source-cost accounting in terms of the packaged projected steps. -/
theorem cost_le_projectedSteps_cost_add_one
    (S : RawCompressionStep n r)
    (D : RawDissection S.before)
    (hS : S.IsValid)
    (cut : Nat)
    (hcut : S.path.HasDissectionCut D cut) :
    S.cost <=
      (S.bottomProjectedStep D hS cut hcut).cost +
        (S.topProjectedStep D hS cut hcut).cost + 1 := by
  unfold cost
  exact S.path.sourceCost_le_projection_edgeCosts_add_one D hS.1.2.2.1 cut hcut

end RawCompressionStep

namespace RawCompressionExecution

variable {m n r : Nat}

/-- Sum of source costs of all raw steps in an execution. -/
noncomputable def stepCostSum (E : RawCompressionExecution m n r) : Nat :=
  ∑ i : Fin m, (E.step i).cost

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

/-- Construct top packing from the exact multiplicative top-cardinality bound. -/
noncomputable def topPacking_of_top_card_mul_pow_le
    (hF : F.IsRankValid)
    (s : Nat)
    (hpack : (dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n) :
    TopPacking F hF s := by
  classical
  let T := (dissection F hF s).topFinset
  let A := T × Fin (2 ^ (s + 1))
  have hcardA : Fintype.card A = T.card * 2 ^ (s + 1) := by
    simp [A]
  have hcard :
      Fintype.card A <= Fintype.card (Fin n) := by
    rw [hcardA]
    simpa [T] using hpack
  let e : A ↪ Fin n := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact {
    pack := fun v j => e (v, j)
    injective_pack := by
      intro p q hpq
      exact e.injective hpq
  }

/-- A failed multiplicative top-cardinality bound rules out `TopPacking`. -/
theorem not_topPacking_of_top_card_mul_pow_gt
    (hF : F.IsRankValid)
    (s : Nat)
    (hgt : n < (dissection F hF s).topFinset.card * 2 ^ (s + 1)) :
    TopPacking F hF s -> False := by
  intro P
  exact (Nat.not_lt_of_ge (top_card_mul_pow_le F hF s P)) hgt

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

/-- Direct rank-threshold packing supplies the `TopPacking` witness. -/
noncomputable def topPacking_of_rankThresholdPacking
    (hF : F.IsRankValid)
    (hpack : F.HasRankThresholdPacking)
    (s : Nat) :
    TopPacking F hF s := by
  have hcard :
      (dissection F hF s).topFinset.card * 2 ^ (s + 1) <= n := by
    have hfinset : (dissection F hF s).topFinset = F.highRankFinset s := by
      ext v
      simp [RawRankedForest.highRankFinset, RawDissection.topFinset,
        RawDissection.IsTop, dissection, topPred]
    rw [hfinset]
    exact hpack s
  exact topPacking_of_top_card_mul_pow_le F hF s hcard

end RankThresholdDissection

end ConcreteSourceModel

end PathCompressionDigestion
