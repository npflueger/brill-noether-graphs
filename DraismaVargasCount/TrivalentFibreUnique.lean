module

public import DraismaVargasCount.BallotResidues

@[expose] public section

/-!
# No target vertex carries two surviving source vertices

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: since `T` is a tree, `φ` is
injective on the spine path `P`.

`BranchSharedDirection.leafAvoidingSeparated_of_trivalentFibreUnique` reduces
`SpineSingleColumn.LeafAvoidingSeparated` -- the hypothesis `hSep` of
`BallotResidues.diagonalClassification_genusSix_of_two_residues` -- to its
hypothesis `hTrivalent`: *no trivalent target vertex carries two distinct
surviving source vertices.*  This module proves `hTrivalent`, and in fact the
same statement above **every non-leaf** target vertex, **for every member of the
caterpillar fibre at every `m`**, with no `Open`, `HasOddMult`, `Diagonal` or
genericity hypothesis.  Hence `hSep` holds at every member, and
`DiagonalClassification 2` rests on `hSupply` alone.  `CaterpillarAllMembers`
uses `leafAvoidingSeparated` for the base count over the caterpillar of loops
(step 1 of `DraismaVargasCount/Assembly.lean`).

## The route: a count and a tree rank, not a walk across rows

Part II's route joins two source vertices by a path in the loop-deleted stable
tree, maps it to a non-backtracking walk in `T`, and uses that a tree has no
closed non-backtracking walk.  Formalized directly, that needs the stable graph
as a tree and a walk formalism across rows.  The route taken here needs
neither.  It replaces *connectivity
of the source* (the global input of the path argument) by an **Euler count**,
and the walk by a **tree rank** of the target (`TargetGeodesic.TreeRank`, whose
`high_injective` field says every target vertex is the larger end of at most one
edge).

1. **Local injectivity** (§1, `isLeafOcc_of_share`).  Two distinct surviving
   occurrences at one source vertex above one target edge force that edge to
   meet a leaf.  Surviving valency three: `BranchSharedDirection` §3 (the pair is
   the lollipop hairpin, above the leaf edge).  Surviving valency two:
   change-minimality gives `r ≤ 3 - val`, so above a non-leaf `r ≤ 1`, and
   `RowWalk.target_ne_of_localRamification_le_one` forbids sharing.
2. **The count** (§3).  With `V` surviving source vertices, `E` surviving
   occurrences and `4m + 2` branch vertices (`member.ident.vertex`), the
   handshake and the valency trichotomy give `E = V + 2m + 1`.  The surviving
   occurrences above leaf edges number at most twice the surviving vertices
   above leaves (each leaf-side vertex sees only the leaf hairpin, two
   occurrences), and those vertices number at most `leafCount = 2m + 2`
   (`LollipopDivalent.leafCount_eq_catCore`, uniqueness above a leaf being
   `BranchSharedDirection.eq_of_target_eq_of_leaf`).  Every other surviving
   occurrence is sent to its end over the *higher-ranked* target end; by
   `high_injective` and (1) this is injective and lands on surviving vertices
   over non-leaves.  Combining: **all but at most one surviving source vertex
   over a non-leaf is the high end of a non-leaf occurrence**.
3. **The descent** (§4).  Strong induction on the rank of the common image.
   If both `X` and `Y` have an occurrence down, the two occurrences lie above the
   one edge of `T` whose high end is the common image, their low ends lie over
   one vertex of smaller rank, so coincide by induction, and (1) at that common
   low end is violated.  If one of them has no occurrence down it is the unique
   exception of (2), which is the rank-minimal surviving vertex over a
   non-leaf; the other then has an occurrence down to a vertex of still smaller
   rank, which is absurd.

## What is proved

* §1 `IsLeafOcc`, `isLeafOcc_of_mem`, **`isLeafOcc_of_share`** -- local
  injectivity away from the leaf edges, at every surviving source vertex.
* §2 `highVertex`, `lowVertex` and their incidence and target lemmas.
* §3 `card_nonDanglingEdges_eq`, `card_leafSurv_le`, `card_leafOccs_le`,
  `card_innerOccs_le`, **`card_innerSurv_sdiff_le_one`**.
* §4 **`eq_of_target_eq_of_not_leaf`** -- above every non-leaf target vertex of
  every caterpillar member at most one source vertex survives;
  `fibreVertexUnique` -- the same above every target vertex;
  **`trivalentFibreUnique`** -- `hTrivalent` verbatim.
* §5 **`leafAvoidingSeparated`** -- `SpineSingleColumn.LeafAvoidingSeparated m
  member` for **every** member at **every** `m`; `diagonal` -- the `diagonal`
  field of `DiagonalClassification m` at every `m`; **`hSep_genusSix`** in the
  binder shape of `BallotResidues.diagonalClassification_genusSix_of_two_residues`;
  `diagonalClassification_genusSix_of_supply` (only `hSupply` remains); a
  non-vacuity `example` at the caterpillar member.  `leafAvoidingSeparated` is what
  the base count `CaterpillarAllMembers` consumes.

## Scope

* `hSupply` is **not** proved here; it is a hypothesis of
  `diagonalClassification_genusSix_of_supply`.
* Nothing here constructs the loop-deleted stable tree or a walk across rows,
  because the count makes them unnecessary for this statement; the spine
  *path* itself is not built here.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `decide`, no `#eval`.
-/

namespace DraismaVargas.Count.TrivalentFibreUnique

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.TargetGeodesic

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  Local injectivity away from the leaf edges -/

section Local

/-- A target occurrence **meets a leaf**: one of its two stored ends is a leaf.
Interface: equivalent to `∃ v, IsLeafVertex target v ∧ edge ∈ incidentEdges v`
(`isLeafOcc_of_mem` is one direction; the other is the definition). -/
def IsLeafOcc (target : CFGraph.{0}) (edge : target.edges) : Prop :=
  IsLeafVertex target (edge : target.V × target.V).1 ∨
    IsLeafVertex target (edge : target.V × target.V).2

theorem isLeafOcc_of_mem {target : CFGraph.{0}} {vertex : target.V}
    (hLeaf : IsLeafVertex target vertex) {edge : target.edges}
    (hMem : edge ∈ GluingDatum.incidentEdges vertex) : IsLeafOcc target edge := by
  rcases fst_eq_or_snd_eq_of_mem_incidentEdges hMem with h | h
  · exact Or.inl (h ▸ hLeaf)
  · exact Or.inr (h ▸ hLeaf)

/-- **Local injectivity away from the leaf edges.**  Two distinct surviving
occurrences at one source vertex lying above one target edge force that edge to
meet a leaf.  At surviving valency three this is `BranchSharedDirection` §3 (the
pair is a lollipop hairpin above its leaf edge); at surviving valency two,
change-minimality bounds the local ramification by `3 - val ≤ 1` above a
non-leaf, and `RowWalk.target_ne_of_localRamification_le_one` then forbids the
sharing. -/
theorem isLeafOcc_of_share (member : FibreMember (catCore m) request (m + 2))
    {Z : member.data.SourceVertex} {a b : member.data.SourceEdge} (hab : a ≠ b)
    (haS : ¬ IsDangling member.data a) (haI : Incident member.data a Z)
    (hbS : ¬ IsDangling member.data b) (hbI : Incident member.data b Z)
    (hShare : (a.1.1 : member.target.edges) = b.1.1) :
    IsLeafOcc member.target a.1.1 := by
  classical
  have hTwo : 2 ≤ nonDanglingValency member.data Z := by
    have hlt : 1 < (SpineSingleColumn.survivorsAt member.data Z).card :=
      Finset.one_lt_card.mpr
        ⟨⟨a, haI⟩, SpineSingleColumn.mem_survivorsAt _ haS,
          ⟨b, hbI⟩, SpineSingleColumn.mem_survivorsAt _ hbS,
          fun h ↦ hab (congrArg Subtype.val h)⟩
    rwa [SpineSingleColumn.card_survivorsAt] at hlt
  rcases member.fullDim.nonDanglingValency_trichotomy Z with h | h | h
  · omega
  · by_contra hNot
    have hMem : (a.1.1 : member.target.edges) ∈ GluingDatum.incidentEdges Z.1.1 :=
      IndexPattern.target_mem_of_incident haI
    have hNotLeaf : (GluingDatum.incidentEdges Z.1.1).card ≠ 1 := fun hOne ↦
      hNot (isLeafOcc_of_mem hOne hMem)
    have hNonneg := member.data.localRamification_nonneg Z.1.1
      (member.fullDim.valid.2 Z.1.1) ⟨Z.1.2, Z.2⟩
    have hLe := IndexPattern.localRamification_le_targetChange member.fullDim
      (wall := Z.1.1) ⟨Z.1.2, Z.2⟩
    rw [IndexPattern.targetChange_eq_three_sub_valency member.fullDim Z.1.1] at hLe
    have hCardPos : 0 < (GluingDatum.incidentEdges Z.1.1).card :=
      Finset.card_pos.mpr ⟨_, hMem⟩
    exact RowWalk.target_ne_of_localRamification_le_one member.fullDim.danglingEdgeNoGlue h
      (by omega) haS haI hbS hbI hab hShare
  · obtain ⟨slot, hLoop, -, hLeafEdge, -, -⟩ :=
      BranchSharedDirection.exists_loopSlot_of_share_at_branch member h hab haS haI hbS hbI
        hShare
    rw [hLeafEdge]
    exact isLeafOcc_of_mem (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
      (leafEdge_mem (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop))

end Local

/-! ## 2.  The high and low source ends of an occurrence -/

section Ends

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-- The source end of `edge` lying over the target end of larger rank. -/
noncomputable def highVertex (A : TreeRank target) (edge : data.SourceEdge) :
    data.SourceVertex := by
  classical
  exact if ((data.sourceEnds edge).1.1.1 : target.V) = A.high edge.1.1 then
    (data.sourceEnds edge).1 else (data.sourceEnds edge).2

/-- The source end of `edge` lying over the target end of smaller rank. -/
noncomputable def lowVertex (A : TreeRank target) (edge : data.SourceEdge) :
    data.SourceVertex := by
  classical
  exact if ((data.sourceEnds edge).1.1.1 : target.V) = A.low edge.1.1 then
    (data.sourceEnds edge).1 else (data.sourceEnds edge).2

theorem sourceEnds_fst_target (edge : data.SourceEdge) :
    ((data.sourceEnds edge).1.1.1 : target.V) = (edge.1.1 : target.V × target.V).1 := rfl

theorem sourceEnds_snd_target (edge : data.SourceEdge) :
    ((data.sourceEnds edge).2.1.1 : target.V) = (edge.1.1 : target.V × target.V).2 := rfl

theorem incident_highVertex (A : TreeRank target) (edge : data.SourceEdge) :
    Incident data edge (highVertex A edge) := by
  classical
  unfold highVertex
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem incident_lowVertex (A : TreeRank target) (edge : data.SourceEdge) :
    Incident data edge (lowVertex A edge) := by
  classical
  unfold lowVertex
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem highVertex_target (A : TreeRank target) (edge : data.SourceEdge) :
    ((highVertex A edge).1.1 : target.V) = A.high edge.1.1 := by
  classical
  unfold highVertex
  split_ifs with h
  · exact h
  · rw [sourceEnds_snd_target]
    rw [sourceEnds_fst_target] at h
    rcases A.ends edge.1.1 with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd h1 h

theorem lowVertex_target (A : TreeRank target) (edge : data.SourceEdge) :
    ((lowVertex A edge).1.1 : target.V) = A.low edge.1.1 := by
  classical
  unfold lowVertex
  split_ifs with h
  · exact h
  · rw [sourceEnds_snd_target]
    rw [sourceEnds_fst_target] at h
    rcases A.ends edge.1.1 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 h
    · exact h2

theorem rank_lowVertex_lt (A : TreeRank target) (edge : data.SourceEdge) :
    A.rank (lowVertex A edge).1.1 < A.rank (highVertex A edge).1.1 := by
  rw [lowVertex_target, highVertex_target]
  exact A.rank_low_lt edge.1.1

/-- The source end of `edge` over one of its leaf ends, when it has one. -/
noncomputable def leafVertex (edge : data.SourceEdge) : data.SourceVertex := by
  classical
  exact if IsLeafVertex target ((data.sourceEnds edge).1.1.1 : target.V) then
    (data.sourceEnds edge).1 else (data.sourceEnds edge).2

theorem incident_leafVertex (edge : data.SourceEdge) :
    Incident data edge (leafVertex edge) := by
  classical
  unfold leafVertex
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem isLeafVertex_leafVertex {edge : data.SourceEdge}
    (hLeaf : IsLeafOcc target edge.1.1) :
    IsLeafVertex target ((leafVertex edge : data.SourceVertex).1.1 : target.V) := by
  classical
  unfold leafVertex
  split_ifs with h
  · exact h
  · rw [sourceEnds_snd_target]
    rw [sourceEnds_fst_target] at h
    rcases hLeaf with h' | h'
    · exact absurd h' h
    · exact h'

end Ends

/-! ## 3.  The count -/

section Count

variable (member : FibreMember (catCore m) request (m + 2))

/-- The surviving source vertices. -/
noncomputable def surv : Finset member.data.SourceVertex := by
  classical
  exact Finset.univ.filter fun X ↦ 0 < nonDanglingValency member.data X

/-- The surviving source vertices over a leaf. -/
noncomputable def leafSurv : Finset member.data.SourceVertex := by
  classical
  exact (surv member).filter fun X ↦ IsLeafVertex member.target X.1.1

/-- The surviving source vertices over a non-leaf. -/
noncomputable def innerSurv : Finset member.data.SourceVertex := by
  classical
  exact (surv member).filter fun X ↦ ¬ IsLeafVertex member.target X.1.1

/-- The surviving occurrences above an edge meeting a leaf. -/
noncomputable def leafOccs : Finset member.data.SourceEdge := by
  classical
  exact (nonDanglingEdges member.data).filter fun a ↦ IsLeafOcc member.target a.1.1

/-- The surviving occurrences above an edge meeting no leaf. -/
noncomputable def innerOccs : Finset member.data.SourceEdge := by
  classical
  exact (nonDanglingEdges member.data).filter fun a ↦ ¬ IsLeafOcc member.target a.1.1

variable {member}

theorem mem_surv {X : member.data.SourceVertex} :
    X ∈ surv member ↔ 0 < nonDanglingValency member.data X := by
  classical
  unfold surv
  simp

theorem mem_leafSurv {X : member.data.SourceVertex} :
    X ∈ leafSurv member ↔
      0 < nonDanglingValency member.data X ∧ IsLeafVertex member.target X.1.1 := by
  classical
  unfold leafSurv
  rw [Finset.mem_filter, mem_surv]

theorem mem_innerSurv {X : member.data.SourceVertex} :
    X ∈ innerSurv member ↔
      0 < nonDanglingValency member.data X ∧ ¬ IsLeafVertex member.target X.1.1 := by
  classical
  unfold innerSurv
  rw [Finset.mem_filter, mem_surv]

theorem mem_leafOccs {a : member.data.SourceEdge} :
    a ∈ leafOccs member ↔ ¬ IsDangling member.data a ∧ IsLeafOcc member.target a.1.1 := by
  classical
  unfold leafOccs
  rw [Finset.mem_filter, mem_nonDanglingEdges]

theorem mem_innerOccs {a : member.data.SourceEdge} :
    a ∈ innerOccs member ↔
      ¬ IsDangling member.data a ∧ ¬ IsLeafOcc member.target a.1.1 := by
  classical
  unfold innerOccs
  rw [Finset.mem_filter, mem_nonDanglingEdges]

variable (member)

/-- **The Euler count.**  `E = V + 2m + 1`: the handshake `Σ nd = 2E`, the
valency trichotomy `nd ∈ {0, 2, 3}`, and the `4m + 2` branch vertices of
`member.ident.vertex`. -/
theorem card_nonDanglingEdges_eq :
    (nonDanglingEdges member.data).card = (surv member).card + (2 * m + 1) := by
  classical
  have hHand := Trivalence.sum_nonDanglingValency member.data
  have hPoint : ∀ X : member.data.SourceVertex, nonDanglingValency member.data X =
      2 * (if 0 < nonDanglingValency member.data X then 1 else 0) +
        (if 3 ≤ nonDanglingValency member.data X then 1 else 0) := by
    intro X
    rcases member.fullDim.nonDanglingValency_trichotomy X with h | h | h <;> simp [h]
  have hSurv : (surv member).card = ∑ X : member.data.SourceVertex,
      (if 0 < nonDanglingValency member.data X then 1 else 0) := by
    unfold surv
    rw [Finset.card_filter]
  have hBr : ((Finset.univ : Finset member.data.SourceVertex).filter
      fun X ↦ 3 ≤ nonDanglingValency member.data X).card = ∑ X : member.data.SourceVertex,
        (if 3 ≤ nonDanglingValency member.data X then 1 else 0) :=
    Finset.card_filter _ _
  rw [Finset.sum_congr rfl fun X _ ↦ hPoint X, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hHand
  have hBranch : ((Finset.univ : Finset member.data.SourceVertex).filter
      fun X ↦ 3 ≤ nonDanglingValency member.data X).card = 4 * m + 2 := by
    have hCard := Fintype.card_congr member.ident.vertex
    rw [Fintype.card_fin] at hCard
    have hSubtype : Fintype.card (StableGraphIncidence.BranchVertex member.data) =
        ((Finset.univ : Finset member.data.SourceVertex).filter
          fun X ↦ 3 ≤ nonDanglingValency member.data X).card :=
      Fintype.card_subtype _
    omega
  omega

/-- At most `2m + 2` surviving source vertices lie over leaves: one per leaf
(`BranchSharedDirection.eq_of_target_eq_of_leaf`), and there are `2m + 2`
leaves (`LollipopDivalent.leafCount_eq_catCore`). -/
theorem card_leafSurv_le : (leafSurv member).card ≤ 2 * m + 2 := by
  classical
  rw [← LollipopDivalent.leafCount_eq_catCore m member]
  refine Finset.card_le_card_of_injOn (fun X ↦ (X.1.1 : member.target.V)) ?_ ?_
  · intro X hX
    exact (mem_leafVertices _).mpr (mem_leafSurv.mp hX).2
  · intro X hX Y hY hXY
    obtain ⟨hXpos, hXleaf⟩ := mem_leafSurv.mp hX
    obtain ⟨hYpos, -⟩ := mem_leafSurv.mp hY
    exact BranchSharedDirection.eq_of_target_eq_of_leaf member hXY hXleaf hXpos hYpos

/-- The surviving occurrences above leaf edges number at most twice the surviving
vertices over leaves: send each to its end over a leaf; the fibre over a vertex
`X` above a leaf lies in `LeafFibre.leafSurvivors`, which has two elements. -/
theorem card_leafOccs_le : (leafOccs member).card ≤ 2 * (leafSurv member).card := by
  classical
  have hMaps : ∀ a ∈ leafOccs member, leafVertex a ∈ leafSurv member := by
    intro a ha
    obtain ⟨haS, haLeaf⟩ := mem_leafOccs.mp ha
    exact mem_leafSurv.mpr ⟨LollipopBridgeFibre.nonDanglingValency_pos_of_survivor haS
      (incident_leafVertex a), isLeafVertex_leafVertex haLeaf⟩
  have hFibre : ∀ X ∈ leafSurv member,
      ((leafOccs member).filter fun a ↦ leafVertex a = X).card ≤ 2 := by
    intro X hX
    have hLeaf := (mem_leafSurv.mp hX).2
    refine le_of_le_of_eq (Finset.card_le_card fun a ha ↦ ?_)
      (leafSurvivors_card (data := member.data) member.fullDim hLeaf)
    obtain ⟨ha, hEq⟩ := Finset.mem_filter.mp ha
    have haS := (mem_leafOccs.mp ha).1
    have hI : Incident member.data a X := hEq ▸ incident_leafVertex a
    exact (mem_leafSurvivors hLeaf).mpr
      ⟨haS, eq_leafEdge_of_mem hLeaf (IndexPattern.target_mem_of_incident hI)⟩
  exact Finset.card_le_mul_card_image_of_maps_to hMaps 2 hFibre

variable (A : TreeRank member.target)

/-- **The high end is injective on the inner occurrences, and lands over a
non-leaf.**  Two inner occurrences with one high end `Z` lie above the unique
target edge whose larger end is the image of `Z` (`TreeRank.high_injective`), so
by local injectivity (§1) they coincide. -/
theorem card_innerOccs_le :
    (innerOccs member).card = ((innerOccs member).image (highVertex A)).card ∧
      (innerOccs member).image (highVertex A) ⊆ innerSurv member := by
  classical
  refine ⟨(Finset.card_image_of_injOn ?_).symm, ?_⟩
  · intro a ha b hb hab
    obtain ⟨haS, haInner⟩ := mem_innerOccs.mp ha
    obtain ⟨hbS, -⟩ := mem_innerOccs.mp hb
    have hTarget : (a.1.1 : member.target.edges) = b.1.1 := by
      apply A.high_injective
      show A.high a.1.1 = A.high b.1.1
      rw [← highVertex_target A a, ← highVertex_target A b]
      exact congrArg (fun X : member.data.SourceVertex ↦ (X.1.1 : member.target.V)) hab
    by_contra hne
    have hbI : Incident member.data b (highVertex A a) := by
      have h : highVertex A a = highVertex A b := hab
      rw [h]; exact incident_highVertex A b
    exact haInner (isLeafOcc_of_share member hne haS (incident_highVertex A a) hbS hbI
      hTarget)
  · intro X hX
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨haS, haInner⟩ := mem_innerOccs.mp ha
    refine mem_innerSurv.mpr ⟨LollipopBridgeFibre.nonDanglingValency_pos_of_survivor haS
      (incident_highVertex A a), fun hLeaf ↦ haInner (isLeafOcc_of_mem hLeaf
        (IndexPattern.target_mem_of_incident (incident_highVertex A a)))⟩

/-- **All but at most one surviving vertex over a non-leaf is the high end of an
inner occurrence.** -/
theorem card_innerSurv_sdiff_le_one :
    (innerSurv member \ (innerOccs member).image (highVertex A)).card ≤ 1 := by
  classical
  obtain ⟨hInj, hSub⟩ := card_innerOccs_le member A
  have hE := card_nonDanglingEdges_eq member
  have hL := card_leafSurv_le member
  have hLO := card_leafOccs_le member
  have hSplitV : (leafSurv member).card + (innerSurv member).card = (surv member).card := by
    unfold leafSurv innerSurv
    exact Finset.card_filter_add_card_filter_not _
  have hSplitE : (leafOccs member).card + (innerOccs member).card =
      (nonDanglingEdges member.data).card := by
    unfold leafOccs innerOccs
    exact Finset.card_filter_add_card_filter_not _
  rw [Finset.card_sdiff_of_subset hSub]
  omega

end Count

/-! ## 4.  The descent: one surviving source vertex over each non-leaf -/

section Descent

variable (member : FibreMember (catCore m) request (m + 2))

/-- **Above every non-leaf target vertex at most one source vertex survives.**
Strong induction on the rank of the common image, over a tree rank of the
target: two survivors with occurrences down have their low ends over one vertex
of smaller rank, equal by induction, where §1 is violated; a survivor with no
occurrence down is the unique exception of §3, which is rank-minimal, and the
other survivor's occurrence down would go lower still. -/
theorem eq_of_target_eq_of_not_leaf {X Y : member.data.SourceVertex}
    (hTarget : (X.1.1 : member.target.V) = (Y.1.1 : member.target.V))
    (hNotLeaf : ¬ IsLeafVertex member.target (X.1.1 : member.target.V))
    (hX : 0 < nonDanglingValency member.data X)
    (hY : 0 < nonDanglingValency member.data Y) :
    X = Y := by
  classical
  obtain ⟨A⟩ := exists_treeRank member.target member.fullDim.targetConnected
    member.fullDim.targetGenus
  set N := innerSurv member with hN
  set Up := (innerOccs member).image (highVertex A) with hUp
  have hSub : Up ⊆ N := (card_innerOccs_le member A).2
  have hOne : (N \ Up).card ≤ 1 := card_innerSurv_sdiff_le_one member A
  -- an element of `Up` has an inner occurrence down, to an element of `N`
  have hDown : ∀ Z ∈ Up, ∃ a ∈ innerOccs member, highVertex A a = Z ∧
      lowVertex A a ∈ N ∧ A.rank (lowVertex A a).1.1 < A.rank Z.1.1 := by
    intro Z hZ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨haS, haInner⟩ := mem_innerOccs.mp ha
    refine ⟨a, ha, rfl, mem_innerSurv.mpr ⟨LollipopBridgeFibre.nonDanglingValency_pos_of_survivor
      haS (incident_lowVertex A a), fun hLeaf ↦ haInner (isLeafOcc_of_mem hLeaf
        (IndexPattern.target_mem_of_incident (incident_lowVertex A a)))⟩,
      rank_lowVertex_lt A a⟩
  -- the exceptions are rank-minimal in `N`
  have hMin : ∀ Z ∈ N \ Up, ∀ W ∈ N, A.rank Z.1.1 ≤ A.rank W.1.1 := by
    intro Z hZ W hW
    have hNe : N.Nonempty := ⟨W, hW⟩
    obtain ⟨M, hMN, hMmin⟩ := Finset.exists_min_image N (fun V ↦ A.rank V.1.1) hNe
    have hMUp : M ∉ Up := by
      intro hMUp
      obtain ⟨a, -, -, hLowN, hLt⟩ := hDown M hMUp
      exact absurd (hMmin _ hLowN) (not_le.mpr hLt)
    have hZM : Z = M := Finset.card_le_one.mp hOne Z hZ M (Finset.mem_sdiff.mpr ⟨hMN, hMUp⟩)
    rw [hZM]
    exact hMmin W hW
  -- the induction
  have hMain : ∀ n : ℕ, ∀ X Y : member.data.SourceVertex, X ∈ N → Y ∈ N →
      A.rank X.1.1 = n → (X.1.1 : member.target.V) = Y.1.1 → X = Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X Y hXN hYN hRank hXY
      by_contra hne
      by_cases hXUp : X ∈ Up
      · by_cases hYUp : Y ∈ Up
        · obtain ⟨a, ha, haX, haLow, haLt⟩ := hDown X hXUp
          obtain ⟨b, hb, hbY, hbLow, -⟩ := hDown Y hYUp
          obtain ⟨haS, haInner⟩ := mem_innerOccs.mp ha
          obtain ⟨hbS, -⟩ := mem_innerOccs.mp hb
          have hEdge : (a.1.1 : member.target.edges) = b.1.1 := by
            apply A.high_injective
            show A.high a.1.1 = A.high b.1.1
            rw [← highVertex_target A a, ← highVertex_target A b, haX, hbY]
            exact hXY
          have hLowTarget : ((lowVertex A a).1.1 : member.target.V) = (lowVertex A b).1.1 := by
            rw [lowVertex_target, lowVertex_target, hEdge]
          have hLowEq : lowVertex A a = lowVertex A b :=
            ih _ (hRank ▸ haLt) _ _ haLow hbLow rfl hLowTarget
          have hab : a ≠ b := by
            intro hab
            apply hne
            rw [← haX, ← hbY, hab]
          have hbI : Incident member.data b (lowVertex A a) := by
            rw [hLowEq]; exact incident_lowVertex A b
          exact haInner (isLeafOcc_of_share member hab haS (incident_lowVertex A a) hbS hbI
            hEdge)
        · obtain ⟨a, -, haX, haLow, haLt⟩ := hDown X hXUp
          have hLe := hMin Y (Finset.mem_sdiff.mpr ⟨hYN, hYUp⟩) _ haLow
          rw [hXY] at haLt
          omega
      · by_cases hYUp : Y ∈ Up
        · obtain ⟨b, -, hbY, hbLow, hbLt⟩ := hDown Y hYUp
          have hLe := hMin X (Finset.mem_sdiff.mpr ⟨hXN, hXUp⟩) _ hbLow
          rw [← hXY] at hbLt
          omega
        · exact hne (Finset.card_le_one.mp hOne X (Finset.mem_sdiff.mpr ⟨hXN, hXUp⟩) Y
            (Finset.mem_sdiff.mpr ⟨hYN, hYUp⟩))
  exact hMain _ X Y (mem_innerSurv.mpr ⟨hX, hNotLeaf⟩)
    (mem_innerSurv.mpr ⟨hY, hTarget ▸ hNotLeaf⟩) rfl hTarget

/-- **No target vertex carries two surviving source vertices**, at every member:
the hypothesis `hUnique` of
`BranchSharedDirection.leafAvoidingSeparated_of_fibreVertexUnique`, verbatim. -/
theorem fibreVertexUnique :
    ∀ X Y : member.data.SourceVertex,
      (X.1.1 : member.target.V) = (Y.1.1 : member.target.V) →
        0 < nonDanglingValency member.data X → 0 < nonDanglingValency member.data Y →
          X = Y := by
  intro X Y hTarget hX hY
  by_cases hLeaf : IsLeafVertex member.target (X.1.1 : member.target.V)
  · exact BranchSharedDirection.eq_of_target_eq_of_leaf member hTarget hLeaf hX hY
  · exact eq_of_target_eq_of_not_leaf member hTarget hLeaf hX hY

/-- **`hTrivalent`, discharged**: the hypothesis of
`BranchSharedDirection.leafAvoidingSeparated_of_trivalentFibreUnique`, verbatim,
at every member of the caterpillar fibre at every `m`. -/
theorem trivalentFibreUnique :
    ∀ X Y : member.data.SourceVertex,
      (X.1.1 : member.target.V) = (Y.1.1 : member.target.V) →
        (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card = 3 →
          0 < nonDanglingValency member.data X →
            0 < nonDanglingValency member.data Y → X = Y := by
  intro X Y hTarget hCard hX hY
  refine eq_of_target_eq_of_not_leaf member hTarget ?_ hX hY
  intro hLeaf
  have hOne : (GluingDatum.incidentEdges (X.1.1 : member.target.V)).card = 1 := hLeaf
  omega

end Descent

/-! ## 5.  `hSep`, and the assemblies with it removed -/

section Consumers

/-- **`SpineSingleColumn.LeafAvoidingSeparated`, at every member and every
`m`**: distinct leaf-avoiding rows never meet a common column. -/
theorem leafAvoidingSeparated (member : FibreMember (catCore m) request (m + 2)) :
    SpineSingleColumn.LeafAvoidingSeparated m member :=
  BranchSharedDirection.leafAvoidingSeparated_of_trivalentFibreUnique member
    (trivalentFibreUnique member)

/-- **The `diagonal` field of `BallotSlopes.DiagonalClassification m`, at every
`m`, unconditionally**: every open odd class over the caterpillar has a diagonal
representative.  This is the diagonality of the caterpillar members at every
genus; the genus-two case is also `BaseCountParity.diagonal_genusTwo`. -/
theorem diagonal (mem : FibreMember (catCore m) request (m + 2)) (hOpen : mem.Open)
    (hOdd : mem.HasOddMult) :
    ∃ rep : FibreMember (catCore m) request (m + 2),
      rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
        GeometricFibre.cls rep = GeometricFibre.cls mem :=
  DiagonalFromSeparation.diagonal_of_leafAvoidingSeparated
    (fun mem' _ _ ↦ leafAvoidingSeparated mem') mem hOpen hOdd

/-- **`hSep`, discharged**, in the exact binder shape of
`BallotResidues.diagonalClassification_genusSix_of_two_residues`. -/
theorem hSep_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem :=
  fun mem _ _ ↦ leafAvoidingSeparated mem

/-- **`DiagonalClassification 2` from `hSupply` alone.** -/
theorem diagonalClassification_genusSix_of_supply {request : Fin (6 * 2 + 3) → ℚ}
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  BallotResidues.diagonalClassification_genusSix_of_two_residues (hSep_genusSix request)
    hSupply

/-- Non-vacuity: `hTrivalent`'s conclusion at the caterpillar member, which is
open and of odd multiplicity at every positive request, and `hSep` there. -/
example {request : Fin (6 * 2 + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot) :
    (caterpillarMember 2 request).Open ∧ (caterpillarMember 2 request).HasOddMult ∧
      SpineSingleColumn.LeafAvoidingSeparated 2 (caterpillarMember 2 request) :=
  ⟨caterpillarMember_open hRequest, caterpillarMember_hasOddMult 2 request,
    hSep_genusSix request _ (caterpillarMember_open hRequest)
      (caterpillarMember_hasOddMult 2 request)⟩

end Consumers

end DraismaVargas.Count.TrivalentFibreUnique
