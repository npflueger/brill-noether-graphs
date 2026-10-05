module

public import DraismaVargasCount.BallotResidues
public import DraismaVargasCount.BlockMatching

@[expose] public section

/-!
# The datum supply `hSupply`: the target layer, and the exact shape of the sheet layer

This module works on the datum-supply hypothesis `hSupply` of
`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`, the
base-pointed form of the uniqueness in part (2) of Part II's `prop-caterpillar-ballot`
(Vargas, arXiv:2609.09109).  It builds on `Count/BallotResidues.lean`.

`hSupply` asks, for every open odd diagonal member `mem` whose core diagonal is
the ballot diagonal of `s`, for a `GeometricDatumIso` from the ballot datum at
`s` to `mem.data`.  A `GeometricDatumIso` is a **target layer** (`targetVertex`,
`targetEdge`, `ends`) plus a **sheet layer** (`vertexPerm`, `edgePerm`, both
partition equations, `compatible`).  This module proves the first outright and
reduces `hSupply` to the second, stated over the first.

## What is proved

**§1--§4, Half 1: the target layer, request-free and core-generic in its
members.**  For *any two* diagonal members `mem₁ mem₂` of the caterpillar fibre
(any two requests, no openness, no oddness, no slope hypothesis),
`targetLayer mem₁ mem₂ hD₁ hD₂ : TargetLayer mem₁.target mem₂.target`, with
`targetLayer_slotEdge` (the target edge over core slot `t` goes to the target
edge over core slot `t`) and `targetLayer_branchImage` (the image of the branch
vertex labelled `c` goes to that of `c`).  The route:
* `slotEdge member : Fin (6m+3) ≃ target.edges` is
  `labelling.targetEdge ∘ slotMap.symm`; `target_eq_slotEdge`: at a diagonal
  member every surviving occurrence on row `t` lies over `slotEdge t`.
* `eq_of_row_eq_of_not_leaf`: a non-leaf row is one occurrence;
  `slotEdge_ends_of_not_leaf`: its target edge joins the branch images of the
  slot's two core ends; `branchImage_tail_mem`: every slot's target edge has the
  branch image of its tail as an end.
* `AbsVertex m = Fin (4m+2) ⊕ LoopSlot m` (core vertices and self-loop slots),
  `absMap` (branch image, resp. the *other* end of the leaf edge), and
  `slotEdge_absEnds`: every target edge has the `absMap`-images of its slot's
  abstract ends as ends.
* `absMap_bijective`: onto because every target vertex is an end of some edge
  (`SegmentWalls.exists_incident_occurrence`), bijective because
  `|AbsVertex m| = 6m + 4 = |V(target)|` (`LollipopLeafRow.card_catCore_loopSlots`,
  `SpinePath.member_vertex_card`).  No tree-isomorphism argument is needed.
* `targetLayer = absEquiv₁⁻¹ ≫ absEquiv₂`, `slotEdge₁⁻¹ ≫ slotEdge₂`; `ends` by
  `UnorderedEnds.symm`/`trans`.  `targetLayer_self_vertex/edge`: with itself it
  is the identity.

**§5, Half 2 stated.**  `SheetLayer first second layer`: the five remaining
fields, with the target maps pinned to `layer`.  `SheetLayer.toIso` is the
`GeometricDatumIso`; `targetLayerOfIso`/`sheetLayerOfIso` go back.
`pullback second layer` pulls a datum back along a target layer, and
**`sheetLayerOfDatumMatching`**: a block-level matching
(`GluingDatum.DatumMatching first (pullback second layer)` -- a
cardinality-preserving bijection of source vertices over every target vertex and
of source occurrences over every target edge, respecting containment) already
*is* a sheet layer, via the block-matching engine `DraismaVargasCount.BlockMatching`.  So the
sheet layer is a **source-graph isomorphism over the target layer**; no
within-block choice is constrained.

**§6, the obligation, its consumer, and the pilots.**
* `SheetLayerSupply m request` -- the named obligation: for every `s` and every
  open odd diagonal `mem` with `mem.coreDiag = ballotCoreDiag m s`, a
  `SheetLayer` between the ballot datum at `s` and `mem.data` **over
  `targetLayer`**.
* **`hSupply_of_sheetLayerSupply`** -- it implies `hSupply`, in the exact binder
  shape of the consumer (every `m`; genus six is `m = 2`).
* `sheetLayer_ballot_self`, `sheetLayer_ballot_zig` -- the obligation at the ballot
  member itself, every `s` (identity permutations; Half 1 is the identity there).
* **`sheetLayer_caterpillarMember`** -- the obligation at the caterpillar member, where
  `BallotResidues.supply_caterpillarMember` gives `hSupply`: Half 1's target layer between
  the zig-zag ballot member and the caterpillar member is the identity of `catTree m`
  (`targetLayer_ballot_caterpillar_vertex/edge`), so the label-respecting form holds
  exactly where `hSupply` was known.
* An `example` inhabiting the antecedent at every positive request.

**§5 cont., the per-vertex census.**
* `blockCard_eq_one_of_nonDanglingValency_eq_zero` -- at every member of every
  fibre, a source vertex off the stable graph is a single sheet (Part I's
  `lemma-dangling-rphi` plus Observation I in the proof of `lemma-dangling-no-glue`).
* `exists_relabel_of_star` (via `starMatching`) -- two partitions each with one
  anchor block and all other blocks singletons are relabellings iff (here: if)
  the anchor blocks have the same size.
* `eq_branchVertex_of_surviving`, `blockCard_eq_one_off_branch` -- above the
  branch image of a loop-free core vertex the only surviving source vertex is the
  branch vertex, so the partition there is a star.
* `blockCard_branch_spine` -- the branch block above an interior spine vertex has
  `2 m(B) + 1 = a + b + 2` with `1/a`, `1/b` the core diagonal on its two spine
  slots.
* **`spine_vertexPartition_relabel`** -- two diagonal members with the same core
  diagonal have, above corresponding interior spine vertices, vertex partitions
  that are relabellings of each other.

**§7, a per-piece census does not suffice.**  `census_not_sufficient`: over the
three-vertex path at degree three there are two gluing data, the first valid,
whose partitions agree up to relabelling at every target vertex and every target
occurrence (over the identity of the target), with **no** `GeometricDatumIso`
between them (one source is connected, the other is not).  `compatible` couples
the permutations along every edge; the sheet layer is not a per-vertex census.

## The sheet-layer obligation

`SheetLayerSupply m request`, equivalently (by `sheetLayerOfDatumMatching`) a
`DatumMatching` between the ballot datum at `s` and `mem.data` pulled back along
`targetLayer`.  Its content, for two diagonal members `D₁ = ballot s`, `D₂ = mem`
with the same core diagonal, is the statement **"the stable part determines the
datum"**:
1. (*stable census*) the surviving source vertices and occurrences of `D₁` and
   `D₂`, with their sizes and incidences, correspond over `targetLayer`
   -- branch vertex `c` to branch vertex `c`, the occurrence of slot `t` to that of
   slot `t`, the two hairpin occurrences and the leaf tip of each loop slot to
   theirs.  Proved here above interior spine vertices (partition level); above leaves
   it is `LeafFibre` (one block of size two, the leaf edge discrete); above the `2m + 2`
   loop vertices (which needs the hairpin: both occurrences of a loop row are incident to
   its branch vertex, via `incidenceCount = 2` and `LeafFibre.leafSurvivors_card`) and for
   occurrence partitions it is not treated here;
2. (*dangling census*) every dangling source vertex is one sheet (proved here,
   every member) and every dangling occurrence has index one
   (`danglingEdgeNoGlue`); so at a surviving vertex `X` over `v` and a direction
   `e` at `v` there are exactly `m(X) - Σ (surviving indices in X over e)`
   dangling occurrences, a number read off the stable census;
3. (*global matching*) each dangling occurrence at `(X, e)` starts a dangling
   tree which, by 2 and harmonicity, is a copy of the whole branch of the target
   beyond `e`, attached to the stable graph at `X` only; match these copies
   branch by branch.  This is the part `census_not_sufficient` shows cannot be
   skipped, and the only part that needs tree-path machinery (the branch of the
   target beyond an edge, and "a sheet's out-region is a full branch").

`SheetLayerSupply` is proved for every `m` in `SheetLayerMatching`
(`SheetLayerMatching.sheetLayerSupply_of_partitionCensus`, from
`PartitionCensusProof.partitionCensus`).

## What is not proved here

* **`hSupply` is not proved here** for any member other than the ballot members and
  the caterpillar member.  `SheetLayerSupply` is a hypothesis of
  `hSupply_of_sheetLayerSupply`; it is proved in `SheetLayerMatching`.
* `SheetLayerSupply` is **stronger** than `hSupply` (its target maps are pinned
  to Half 1's).  The converse implication would need uniqueness of a
  label-respecting target layer; it is not proved.
* The per-vertex census is proved here above interior spine vertices only (vertex
  partitions); not above loop vertices, not for occurrence partitions, and the
  global matching (item 3 above) is not treated here.
* `Open` and `HasOddMult` are carried by `SheetLayerSupply` but unused by
  everything proved here; the target layer uses only `Diagonal`.
-/

namespace DraismaVargas.Count.DiagonalTargetIso

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.EdgeDenominator

/-! ## 1.  Two facts about a single source occurrence -/

section Generic

variable {target : CFGraph} {degree : ℕ}

/-- An endpoint of a source occurrence lies over an endpoint of its target
occurrence. -/
theorem target_of_incident (data : GluingDatum target degree) (edge : data.SourceEdge)
    {vertex : data.SourceVertex} (h : Incident data edge vertex) :
    vertex.1.1 = (edge.1.1 : target.V × target.V).1 ∨
      vertex.1.1 = (edge.1.1 : target.V × target.V).2 := by
  rcases h with h | h
  · exact Or.inl (by rw [← h]; rfl)
  · exact Or.inr (by rw [← h]; rfl)

/-- A source occurrence incident to two distinct source vertices joins them, so
its target occurrence joins their images. -/
theorem target_ends_of_two_incident (data : GluingDatum target degree)
    (edge : data.SourceEdge) {first second : data.SourceVertex} (hne : first ≠ second)
    (h₁ : Incident data edge first) (h₂ : Incident data edge second) :
    (edge.1.1 : target.V × target.V) = (first.1.1, second.1.1) ∨
      (edge.1.1 : target.V × target.V) = (second.1.1, first.1.1) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (h₁.symm.trans h₂) hne
  · left
    exact Prod.ext (by rw [← h₁]; rfl) (by rw [← h₂]; rfl)
  · right
    exact Prod.ext (by rw [← h₂]; rfl) (by rw [← h₁]; rfl)
  · exact absurd (h₁.symm.trans h₂) hne

end Generic

/-! ## 2.  The per-slot target edge and the branch images of a diagonal member -/

section Member

variable {m : ℕ} {y : Fin (6 * m + 3) → ℚ}

/-- The target edge over core slot `t`: the column of the row labelled `t`. -/
noncomputable def slotEdge (member : FibreMember (catCore m) y (m + 2)) :
    Fin (6 * m + 3) ≃ member.target.edges :=
  member.slotMap.symm.trans member.fullDim.labelling.targetEdge

/-- The target vertex under the branch vertex labelled by the core vertex `c`. -/
noncomputable def branchImage (member : FibreMember (catCore m) y (m + 2))
    (c : Fin (4 * m + 2)) : member.target.V :=
  (member.ident.vertex.symm c).1.1.1

/-- The labelling row of a surviving occurrence is `slotMap.symm` of its core slot. -/
theorem labelling_row_eq (member : FibreMember (catCore m) y (m + 2))
    (edge : NonDanglingEdge member.data) :
    member.fullDim.labelling.row edge.stablePath =
      member.slotMap.symm (member.ident.row edge.stablePath) := by
  rw [Equiv.eq_symm_apply, FibreMember.slotMap_apply, Equiv.symm_apply_apply]

/-- At a diagonal member every surviving occurrence on the row of slot `t` lies
over `slotEdge t`. -/
theorem target_eq_slotEdge (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (edge : NonDanglingEdge member.data) :
    edge.1.1.1 = slotEdge member (member.ident.row edge.stablePath) := by
  set r := member.fullDim.labelling.row edge.stablePath with hr
  have hmem : edge.1 ∈ rowEdges member.fullDim.labelling r :=
    (mem_rowEdges _ _ _).mpr ⟨edge.2, rfl⟩
  have hSupport : ∀ j, j ≠ r → GluingDatum.LengthMatrixPresentation.matrix
      member.fullDim.labelling.presentation r j = 0 := fun j hj ↦ hD r j hj
  have hTarget : edge.1.1.1 = member.fullDim.labelling.targetEdge r :=
    NonTrivalentCorner.target_eq_of_supported member.fullDim.labelling hSupport hmem
  rw [hTarget, slotEdge, Equiv.trans_apply, hr, labelling_row_eq]

/-- **A non-leaf row of a diagonal member is one occurrence.**  Two surviving
occurrences on the row of a non-leaf slot coincide
(`NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf`; the non-leaf column is
certified by `SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf`, exactly as
in `BallotResidues.coreDiag_eq_inv_sourceEdgeIndex`). -/
theorem eq_of_row_eq_of_not_leaf (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) {t : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m t)
    {first second : NonDanglingEdge member.data}
    (h₁ : member.ident.row first.stablePath = t)
    (h₂ : member.ident.row second.stablePath = t) : first = second := by
  classical
  set r := member.slotMap.symm t with hr
  have hrow : ∀ edge : NonDanglingEdge member.data, member.ident.row edge.stablePath = t →
      edge.1 ∈ LeafFibre.rowFibre member.fullDim.labelling r
        (member.fullDim.labelling.targetEdge r) := by
    intro edge hedge
    have hl : member.fullDim.labelling.row edge.stablePath = r := by
      rw [labelling_row_eq, hedge]
    have hmem : edge.1 ∈ rowEdges member.fullDim.labelling r :=
      (mem_rowEdges _ _ _).mpr ⟨edge.2, hl⟩
    have hTarget := target_eq_slotEdge member hD edge
    rw [hedge] at hTarget
    exact (EdgeDenominator.mem_rowFibre_iff _ _ _ _).mpr ⟨hmem, hTarget⟩
  have hSupport : ∀ j, j ≠ r → GluingDatum.LengthMatrixPresentation.matrix
      member.fullDim.labelling.presentation r j = 0 := fun j hj ↦ hD r j hj
  have hNonleaf : r ∉ leafColumns member.fullDim.labelling.presentation := by
    intro hcol
    obtain ⟨v, hv, hincid⟩ := (mem_leafColumns _ _).mp hcol
    have hmem : first.1 ∈ rowEdges member.fullDim.labelling r :=
      (mem_rowEdges _ _ _).mpr ⟨first.2, by
        show member.fullDim.labelling.row first.stablePath = r
        rw [labelling_row_eq, h₁]⟩
    have hTarget : first.1.1.1 = member.fullDim.labelling.targetEdge r :=
      NonTrivalentCorner.target_eq_of_supported member.fullDim.labelling hSupport hmem
    have hPasses : PassesAboveLeaf member.fullDim.labelling r :=
      ⟨first.1, hmem, v, hv, by rw [hTarget]; exact hincid⟩
    obtain ⟨slot, hLoop, hEq⟩ :=
      SpineRowLengthWitness.exists_loopSlot_of_passesAboveLeaf member hPasses
    apply hNotLeaf
    have hIs : t = slot := by
      rw [← Equiv.apply_symm_apply member.slotMap t, ← hr, hEq, FibreMember.slotMap_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [hIs]
    exact (LollipopLeafRow.catCore_tail_eq_head_iff m slot).mp hLoop
  obtain ⟨e, _he, hfibre, _hval⟩ :=
    NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf member.fullDim hSupport hNonleaf
  have hf₁ := hrow first h₁
  have hf₂ := hrow second h₂
  rw [hfibre, Finset.mem_singleton] at hf₁ hf₂
  exact Subtype.ext (hf₁.trans hf₂.symm)

/-- The tail of every slot carries a surviving occurrence of that slot's row. -/
theorem coreIncidence_tail_pos (t : Fin (6 * m + 3)) :
    0 < coreIncidence (catCore m) ((catCore m).tail t) t := by
  unfold coreIncidence; rw [ite_eq_left rfl]; omega

theorem coreIncidence_head_pos (t : Fin (6 * m + 3)) :
    0 < coreIncidence (catCore m) ((catCore m).head t) t := by
  unfold coreIncidence
  by_cases h : (catCore m).tail t = (catCore m).head t
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h, ite_eq_left rfl]; omega

/-- **The branch vertex at the tail of a slot sits over an end of its target
edge** (every slot, loop or not). -/
theorem branchImage_tail_mem (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : Fin (6 * m + 3)) :
    (slotEdge member t : member.target.V × member.target.V).1 =
        branchImage member ((catCore m).tail t) ∨
      (slotEdge member t : member.target.V × member.target.V).2 =
        branchImage member ((catCore m).tail t) := by
  obtain ⟨edge, hI, hRow⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
    ((catCore m).tail t) t (coreIncidence_tail_pos t)
  have hT := target_eq_slotEdge member hD edge
  rw [hRow] at hT
  rcases target_of_incident member.data edge.1 hI with h | h
  · left; rw [← hT]; exact h.symm
  · right; rw [← hT]; exact h.symm

/-- **A non-leaf slot's target edge joins the images of its two core ends.** -/
theorem slotEdge_ends_of_not_leaf (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) {t : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m t) :
    (slotEdge member t : member.target.V × member.target.V) =
        (branchImage member ((catCore m).tail t), branchImage member ((catCore m).head t)) ∨
      (slotEdge member t : member.target.V × member.target.V) =
        (branchImage member ((catCore m).head t), branchImage member ((catCore m).tail t)) := by
  have hne : (catCore m).tail t ≠ (catCore m).head t := fun h ↦
    hNotLeaf ((LollipopLeafRow.catCore_tail_eq_head_iff m t).mp h)
  obtain ⟨e₁, hI₁, hR₁⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
    ((catCore m).tail t) t (coreIncidence_tail_pos t)
  obtain ⟨e₂, hI₂, hR₂⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
    ((catCore m).head t) t (coreIncidence_head_pos t)
  have h12 : e₁ = e₂ := eq_of_row_eq_of_not_leaf member hD hNotLeaf hR₁ hR₂
  subst h12
  have hXY : (member.ident.vertex.symm ((catCore m).tail t)).1 ≠
      (member.ident.vertex.symm ((catCore m).head t)).1 := by
    intro h
    exact hne (member.ident.vertex.symm.injective (Subtype.ext h))
  have hT := target_eq_slotEdge member hD e₁
  rw [hR₁] at hT
  rw [← hT]
  exact target_ends_of_two_incident member.data e₁.1 hXY hI₁ hI₂

end Member

/-! ## 3.  The abstract vertex set, and the vertex dictionary of a member -/

section Dictionary

variable {m : ℕ} {y : Fin (6 * m + 3) → ℚ}

variable (m) in
/-- The self-loop slots of `catCore m` (the `g = 2m + 2` leaf edges). -/
abbrev LoopSlot : Type :=
  {t : Fin (6 * m + 3) // (catCore m).tail t = (catCore m).head t}

variable (m) in
/-- **The abstract vertex set of the target tree**: one vertex per core vertex
(its branch image) and one per self-loop slot (the tip of its leaf edge). -/
abbrev AbsVertex : Type := Fin (4 * m + 2) ⊕ LoopSlot m

theorem card_absVertex : Fintype.card (AbsVertex m) = 6 * m + 3 + 1 := by
  rw [Fintype.card_sum, Fintype.card_fin, LollipopLeafRow.card_catCore_loopSlots m]
  omega

variable (m) in
/-- The abstract ends of a slot: its two core ends, or its core end and its tip. -/
def absEnds (t : Fin (6 * m + 3)) : AbsVertex m × AbsVertex m :=
  if h : (catCore m).tail t = (catCore m).head t then
    (Sum.inl ((catCore m).tail t), Sum.inr ⟨t, h⟩)
  else (Sum.inl ((catCore m).tail t), Sum.inl ((catCore m).head t))

/-- The tip of a slot's target edge: its end other than the tail's branch image. -/
noncomputable def tip (member : FibreMember (catCore m) y (m + 2)) (t : Fin (6 * m + 3)) :
    member.target.V :=
  if (slotEdge member t : member.target.V × member.target.V).1 =
      branchImage member ((catCore m).tail t)
  then (slotEdge member t : member.target.V × member.target.V).2
  else (slotEdge member t : member.target.V × member.target.V).1

/-- The vertex dictionary of a member, as a function. -/
noncomputable def absMap (member : FibreMember (catCore m) y (m + 2)) :
    AbsVertex m → member.target.V
  | Sum.inl c => branchImage member c
  | Sum.inr t => tip member t.1

/-- **Every slot's target edge has the dictionary images of its abstract ends as
ends**, in some order. -/
theorem slotEdge_absEnds (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : Fin (6 * m + 3)) :
    (slotEdge member t : member.target.V × member.target.V) =
        (absMap member (absEnds m t).1, absMap member (absEnds m t).2) ∨
      (slotEdge member t : member.target.V × member.target.V) =
        (absMap member (absEnds m t).2, absMap member (absEnds m t).1) := by
  unfold absEnds
  split_ifs with hLoop
  · simp only [absMap, tip]
    rcases branchImage_tail_mem member hD t with h | h
    · rw [ite_eq_left h]
      left
      exact Prod.ext h rfl
    · by_cases h1 : (slotEdge member t : member.target.V × member.target.V).1 =
          branchImage member ((catCore m).tail t)
      · rw [ite_eq_left h1]
        left
        exact Prod.ext h1 rfl
      · rw [ite_eq_right h1]
        right
        exact Prod.ext rfl h
  · exact slotEdge_ends_of_not_leaf member hD
      (fun hL ↦ hLoop ((LollipopLeafRow.catCore_tail_eq_head_iff m t).mpr hL))

/-- The dictionary is onto: every target vertex is an end of some target edge. -/
theorem absMap_surjective (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) : Function.Surjective (absMap member) := by
  intro v
  have := member.fullDim.nontrivial_target
  obtain ⟨e, he⟩ := SegmentWalls.exists_incident_occurrence member.fullDim.targetConnected v
  obtain ⟨t, rfl⟩ := (slotEdge member).surjective e
  rcases slotEdge_absEnds member hD t with h | h <;> rw [h] at he <;>
    rcases he with he | he
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩

/-- **The vertex dictionary is a bijection**: onto, between sets of the same size
(`SpinePath.member_vertex_card`: the target is a tree with `6m + 3` edges). -/
theorem absMap_bijective (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) : Function.Bijective (absMap member) :=
  (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨absMap_surjective member hD,
      by rw [card_absVertex, SpinePath.member_vertex_card member]⟩

/-- The vertex dictionary, as an equivalence. -/
noncomputable def absEquiv (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) : AbsVertex m ≃ member.target.V :=
  Equiv.ofBijective _ (absMap_bijective member hD)

@[simp] theorem absEquiv_apply (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (x : AbsVertex m) : absEquiv member hD x = absMap member x := rfl

theorem unorderedEnds_absEquiv (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (t : Fin (6 * m + 3)) :
    UnorderedEnds (absEquiv member hD) (absEnds m t)
      (slotEdge member t : member.target.V × member.target.V) :=
  slotEdge_absEnds member hD t

end Dictionary

/-! ## 4.  The target layer -/

/-- **The target layer of a `GeometricDatumIso`**: its first three fields. -/
structure TargetLayer (target₁ target₂ : CFGraph) where
  targetVertex : target₁.V ≃ target₂.V
  targetEdge : target₁.edges ≃ target₂.edges
  ends : ∀ edge : target₁.edges,
    UnorderedEnds targetVertex (edge : target₁.V × target₁.V)
      (targetEdge edge : target₂.V × target₂.V)

section Layer

variable {m : ℕ} {y₁ y₂ : Fin (6 * m + 3) → ℚ}

/-- **Half 1: the target layer between two diagonal members.**  No request, no
openness, no oddness and no slope hypothesis: any two diagonal members of the
caterpillar fibre, over any two requests, have isomorphic targets, by an
isomorphism matching the target edge over core slot `t` with the target edge over
core slot `t`, and the branch image of core vertex `c` with that of `c`. -/
noncomputable def targetLayer (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal) :
    TargetLayer mem₁.target mem₂.target where
  targetVertex := (absEquiv mem₁ hD₁).symm.trans (absEquiv mem₂ hD₂)
  targetEdge := (slotEdge mem₁).symm.trans (slotEdge mem₂)
  ends edge := by
    obtain ⟨t, rfl⟩ := (slotEdge mem₁).surjective edge
    have h₁ := (unorderedEnds_absEquiv mem₁ hD₁ t).symm
    have h₂ := unorderedEnds_absEquiv mem₂ hD₂ t
    have h := h₁.trans h₂
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h

/-- The target layer matches slot labels. -/
@[simp] theorem targetLayer_slotEdge (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (t : Fin (6 * m + 3)) :
    (targetLayer mem₁ mem₂ hD₁ hD₂).targetEdge (slotEdge mem₁ t) = slotEdge mem₂ t := by
  simp [targetLayer]

/-- The target layer matches branch images. -/
@[simp] theorem targetLayer_branchImage (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (c : Fin (4 * m + 2)) :
    (targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex (branchImage mem₁ c) = branchImage mem₂ c := by
  have h : (absEquiv mem₁ hD₁).symm (branchImage mem₁ c) = Sum.inl c :=
    (Equiv.symm_apply_eq _).mpr rfl
  simp only [targetLayer, Equiv.trans_apply, h]
  rfl

/-- The target layer of a member with itself is the identity. -/
theorem targetLayer_self_vertex (mem : FibreMember (catCore m) y₁ (m + 2))
    (hD : mem.Diagonal) (v : mem.target.V) :
    (targetLayer mem mem hD hD).targetVertex v = v := by
  simp [targetLayer]

theorem targetLayer_self_edge (mem : FibreMember (catCore m) y₁ (m + 2))
    (hD : mem.Diagonal) (e : mem.target.edges) :
    (targetLayer mem mem hD hD).targetEdge e = e := by
  simp [targetLayer]

end Layer

/-! ## 5.  The sheet layer: the remaining obligation, stated over a fixed target layer -/

section Sheet

variable {target₁ target₂ : CFGraph} {degree : ℕ}

/-- **The sheet layer over a fixed target layer**: the five remaining fields of a
`GeometricDatumIso`, with the target maps pinned to those of `layer`. -/
structure SheetLayer (first : GluingDatum target₁ degree) (second : GluingDatum target₂ degree)
    (layer : TargetLayer target₁ target₂) where
  vertexPerm : target₁.V → Equiv.Perm (Fin degree)
  edgePerm : target₁.edges → Equiv.Perm (Fin degree)
  vertexPartition : ∀ vertex : target₁.V,
    second.vertexPartition (layer.targetVertex vertex) =
      (first.vertexPartition vertex).relabel (vertexPerm vertex)
  edgePartition : ∀ edge : target₁.edges,
    second.edgePartition (layer.targetEdge edge) =
      (first.edgePartition edge).relabel (edgePerm edge)
  compatible : ∀ (edge : target₁.edges) (vertex : target₁.V),
    ((edge : target₁.V × target₁.V).1 = vertex ∨
      (edge : target₁.V × target₁.V).2 = vertex) → ∀ sheet : Fin degree,
    (first.vertexPartition vertex).Rel ((vertexPerm vertex).symm (edgePerm edge sheet)) sheet

/-- A target layer and a sheet layer over it are a `GeometricDatumIso`. -/
def SheetLayer.toIso {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    {layer : TargetLayer target₁ target₂} (sheets : SheetLayer first second layer) :
    GeometricDatumIso first second where
  targetVertex := layer.targetVertex
  targetEdge := layer.targetEdge
  ends := layer.ends
  vertexPerm := sheets.vertexPerm
  edgePerm := sheets.edgePerm
  vertexPartition := sheets.vertexPartition
  edgePartition := sheets.edgePartition
  compatible := sheets.compatible

/-- Conversely a `GeometricDatumIso` is a sheet layer over its own target layer
(so `SheetLayer` loses nothing once the target layer is the right one). -/
def targetLayerOfIso {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second) :
    TargetLayer target₁ target₂ :=
  ⟨iso.targetVertex, iso.targetEdge, iso.ends⟩

def sheetLayerOfIso {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second) :
    SheetLayer first second (targetLayerOfIso iso) :=
  ⟨iso.vertexPerm, iso.edgePerm, iso.vertexPartition, iso.edgePartition, iso.compatible⟩

/-- The identity sheet layer over any target layer that is the identity pointwise. -/
def SheetLayer.ofId (data : GluingDatum target₁ degree) (layer : TargetLayer target₁ target₁)
    (hV : ∀ v, layer.targetVertex v = v) (hE : ∀ e, layer.targetEdge e = e) :
    SheetLayer data data layer where
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    rw [hV]
    exact (Transport.DatumIso.refl data).vertexPartition v
  edgePartition e := by
    rw [hE]
    exact (Transport.DatumIso.refl data).edgePartition e
  compatible _ _ _ _ := rfl

end Sheet

/-! ### The sheet layer is block-level: pulling the second datum back

`SheetLayer` asks for sheet permutations.  By the block-matching engine
(`DraismaVargasCount.BlockMatching`, `GluingDatum.DatumMatching.sheetRelabeling`) it is
enough to give, at every target vertex and occurrence, a cardinality-preserving
bijection of **blocks** -- i.e. of source vertices and source occurrences -- that
respects containment of occurrence blocks in vertex blocks: a source-graph
isomorphism over the target layer.  No within-block choice is constrained. -/

section Pullback

variable {target₁ target₂ : CFGraph} {degree : ℕ}

theorem refines_of_unorderedEnds (second : GluingDatum target₂ degree)
    (layer : TargetLayer target₁ target₂) (edge : target₁.edges) {vertex : target₁.V}
    (hv : (edge : target₁.V × target₁.V).1 = vertex ∨ (edge : target₁.V × target₁.V).2 = vertex) :
    (second.edgePartition (layer.targetEdge edge)).Refines
      (second.vertexPartition (layer.targetVertex vertex)) := by
  have h := (layer.ends edge).incident_iff vertex
  rcases h.mpr hv with h | h
  · rw [← h]; exact second.refines_left _
  · rw [← h]; exact second.refines_right _

/-- The second datum pulled back to the first target along a target layer. -/
def pullback (second : GluingDatum target₂ degree) (layer : TargetLayer target₁ target₂) :
    GluingDatum target₁ degree where
  degree_pos := second.degree_pos
  vertexPartition v := second.vertexPartition (layer.targetVertex v)
  edgePartition e := second.edgePartition (layer.targetEdge e)
  refines_left e := refines_of_unorderedEnds second layer e (Or.inl rfl)
  refines_right e := refines_of_unorderedEnds second layer e (Or.inr rfl)

/-- **A block-level matching gives the sheet layer.** -/
noncomputable def sheetLayerOfDatumMatching {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} {layer : TargetLayer target₁ target₂}
    (matching : GluingDatum.DatumMatching first (pullback second layer)) :
    SheetLayer first second layer where
  vertexPerm v := (matching.vertex v).perm
  edgePerm e := (matching.edge e).perm
  vertexPartition v := (matching.vertex v).relabel_perm.symm
  edgePartition e := (matching.edge e).relabel_perm.symm
  compatible e v hv sheet := by
    rcases hv with h | h
    · subst h
      exact (GluingDatum.DatumMatching.sheetRelabeling matching).compatible_left e sheet
    · subst h
      exact (GluingDatum.DatumMatching.sheetRelabeling matching).compatible_right e sheet

end Pullback

/-! ### The first piece of the per-vertex census

Every source vertex off the stable graph is a single sheet, at every member of
every fibre (Draisma--Vargas Part I, `lemma-dangling-rphi` plus Observation I in the proof
of `lemma-dangling-no-glue`, formalized as
`StableLocalProperties.localRamification_eq_zero_of_forall_isDangling` and
`NonDanglingValency.blockCard_eq_one_of_nonDanglingValency_eq_zero`).  So the only
blocks of size at least two above a target vertex are surviving source vertices. -/

theorem blockCard_eq_one_of_nonDanglingValency_eq_zero {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (member : FibreMember core y degree) (vertex : member.data.SourceVertex)
    (hZero : nonDanglingValency member.data vertex = 0) :
    (member.data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1 := by
  classical
  have hDangling : ∀ edge : IncidentSourceEdge member.data vertex,
      IsDangling member.data edge.1 := by
    intro edge
    by_contra hSurvives
    have hPos : 0 < ((Finset.univ : Finset (IncidentSourceEdge member.data vertex)).filter
        (fun edge ↦ ¬ IsDangling member.data edge.1)).card :=
      Finset.card_pos.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives⟩⟩
    rw [StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency, hZero] at hPos
    exact lt_irrefl 0 hPos
  exact NonDanglingValency.blockCard_eq_one_of_nonDanglingValency_eq_zero member.data
    member.fullDim.danglingEdgeNoGlue vertex
    (StableLocalProperties.localRamification_eq_zero_of_forall_isDangling member.data
      member.fullDim.valid member.fullDim.changeMinimal member.fullDim.labelling
      member.fullDim.det_ne_zero vertex hDangling) hZero

/-! ### Star partitions are determined by the size of their one block

A partition all of whose blocks but one are singletons is determined, up to a
relabelling, by the size of that block.  This is the only way a per-vertex
census can pin a partition, and it is what the census below delivers. -/

section Star

variable {d : ℕ}

theorem repr_eq_self_of_blockCard_eq_one (P : SheetPartition d) {σ : Fin d}
    (h : P.blockCard σ = 1) : P.repr σ = σ := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have h1 : σ ∈ P.block σ := P.self_mem_block σ
  have h2 : P.repr σ ∈ P.block σ := (P.mem_block_iff _ _).mpr (P.rel_repr_right σ)
  rw [ha, Finset.mem_singleton] at h1 h2
  rw [h2, h1]

theorem blockCard_congr' (P : SheetPartition d) {i j : Fin d} (h : P.Rel i j) :
    P.blockCard i = P.blockCard j := by
  unfold SheetPartition.blockCard
  rw [P.block_eq_of_rel h]

theorem card_not_rel (P : SheetPartition d) (x : Fin d) :
    Fintype.card {σ // ¬ P.Rel σ x} = d - P.blockCard x := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
  congr 2
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SheetPartition.mem_block_iff,
    SheetPartition.rel_iff]
  exact eq_comm

/-- **The star block matching**: the anchor block onto the anchor block, and the
singletons onto the singletons by any bijection. -/
noncomputable def starMatching (P Q : SheetPartition d) (x y : Fin d)
    (hCard : Q.blockCard y = P.blockCard x)
    (hP : ∀ σ, ¬ P.Rel σ x → P.blockCard σ = 1)
    (hQ : ∀ σ, ¬ Q.Rel σ y → Q.blockCard σ = 1) :
    SheetPartition.BlockMatching P Q := by
  classical
  let e : {σ // ¬ P.Rel σ x} ≃ {σ // ¬ Q.Rel σ y} :=
    Fintype.equivOfCardEq (by rw [card_not_rel, card_not_rel, hCard])
  refine
    { map := fun σ ↦ if h : P.Rel σ x then Q.repr y else (e ⟨σ, h⟩).1
      map_repr := ?_
      repr_map := ?_
      rel_of_map_eq := ?_
      blockCard_map := ?_ }
  · intro σ
    by_cases hσ : P.Rel σ x
    · have h' : P.Rel (P.repr σ) x := (P.rel_repr_left σ).trans hσ
      rw [dite_eq_left h', dite_eq_left hσ]
    · have hr : P.repr σ = σ := repr_eq_self_of_blockCard_eq_one P (hP σ hσ)
      simp only [hr]
  · intro σ
    by_cases hσ : P.Rel σ x
    · rw [dite_eq_left hσ]
      exact Q.repr_idem y
    · rw [dite_eq_right hσ]
      exact repr_eq_self_of_blockCard_eq_one Q (hQ _ (e ⟨σ, hσ⟩).2)
  · intro i j hEq
    by_cases hi : P.Rel i x <;> by_cases hj : P.Rel j x
    · exact hi.trans hj.symm
    · rw [dite_eq_left hi, dite_eq_right hj] at hEq
      exact absurd (show Q.Rel (e ⟨j, hj⟩).1 y by
        show Q.repr _ = Q.repr y
        rw [← hEq, Q.repr_idem]) (e ⟨j, hj⟩).2
    · rw [dite_eq_right hi, dite_eq_left hj] at hEq
      exact absurd (show Q.Rel (e ⟨i, hi⟩).1 y by
        show Q.repr _ = Q.repr y
        rw [hEq, Q.repr_idem]) (e ⟨i, hi⟩).2
    · rw [dite_eq_right hi, dite_eq_right hj] at hEq
      have := e.injective (Subtype.ext hEq)
      rw [Subtype.mk.injEq] at this
      subst this
      rfl
  · intro σ
    by_cases hσ : P.Rel σ x
    · rw [dite_eq_left hσ, blockCard_congr' Q (Q.rel_repr_left y), hCard, blockCard_congr' P hσ]
    · rw [dite_eq_right hσ, hQ _ (e ⟨σ, hσ⟩).2, hP σ hσ]

/-- Two star partitions with anchor blocks of the same size are relabellings. -/
theorem exists_relabel_of_star (P Q : SheetPartition d) (x y : Fin d)
    (hCard : Q.blockCard y = P.blockCard x)
    (hP : ∀ σ, ¬ P.Rel σ x → P.blockCard σ = 1)
    (hQ : ∀ σ, ¬ Q.Rel σ y → Q.blockCard σ = 1) :
    ∃ π : Equiv.Perm (Fin d), Q = P.relabel π := by
  obtain ⟨π, hπ⟩ := (SheetPartition.BlockMatching.exists_perm_iff_nonempty_blockMatching P Q).mpr
    ⟨starMatching P Q x y hCard hP hQ⟩
  exact ⟨π, hπ.symm⟩

end Star

/-! ### The per-vertex census at every interior spine vertex

At a diagonal member, above the branch image of an interior spine vertex of
`catCore m` the partition is a **star**: the branch vertex's block, every other
block a single sheet; and the branch block has size `(a + b + 1) / 2`, where
`1/a`, `1/b` are the core diagonal on the two spine slots.  So two diagonal
members with the same core diagonal have, above corresponding spine vertices,
partitions that are relabellings of each other. -/

section SpineCensus

variable {m : ℕ} {y y₁ y₂ : Fin (6 * m + 3) → ℚ}

theorem eq_or_eq_of_three_incident {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (edge : data.SourceEdge)
    {X Y Z : data.SourceVertex} (hYZ : Y ≠ Z) (hY : Incident data edge Y)
    (hZ : Incident data edge Z) (hX : Incident data edge X) : X = Y ∨ X = Z := by
  rcases hY with hY | hY <;> rcases hZ with hZ | hZ <;> rcases hX with hX | hX <;>
    first
    | exact Or.inl (hX.symm.trans hY)
    | exact Or.inr (hX.symm.trans hZ)
    | exact absurd (hY.symm.trans hZ) hYZ

/-- The branch vertex labelled `c`. -/
noncomputable def branchVertex (member : FibreMember (catCore m) y (m + 2))
    (c : Fin (4 * m + 2)) : member.data.SourceVertex :=
  (member.ident.vertex.symm c).1

/-- A source vertex on the single occurrence of a non-leaf row is one of the row's
two branch ends. -/
theorem incident_of_not_leaf (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) {t : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m t)
    (edge : NonDanglingEdge member.data) (hRow : member.ident.row edge.stablePath = t)
    {X : member.data.SourceVertex} (hX : Incident member.data edge.1 X) :
    X = branchVertex member ((catCore m).tail t) ∨
      X = branchVertex member ((catCore m).head t) := by
  have hne : (catCore m).tail t ≠ (catCore m).head t := fun h ↦
    hNotLeaf ((LollipopLeafRow.catCore_tail_eq_head_iff m t).mp h)
  obtain ⟨e₁, hI₁, hR₁⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
    ((catCore m).tail t) t (coreIncidence_tail_pos t)
  obtain ⟨e₂, hI₂, hR₂⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
    ((catCore m).head t) t (coreIncidence_head_pos t)
  have h₁ : e₁ = edge := eq_of_row_eq_of_not_leaf member hD hNotLeaf hR₁ hRow
  have h₂ : e₂ = edge := eq_of_row_eq_of_not_leaf member hD hNotLeaf hR₂ hRow
  have hI₂' : Incident member.data e₁.1 (member.ident.vertex.symm ((catCore m).head t)).1 := by
    rw [h₁, ← h₂]; exact hI₂
  have hX' : Incident member.data e₁.1 X := by rw [h₁]; exact hX
  have hXY : branchVertex member ((catCore m).tail t) ≠
      branchVertex member ((catCore m).head t) := by
    intro h
    exact hne (member.ident.vertex.symm.injective (Subtype.ext h))
  exact eq_or_eq_of_three_incident member.data e₁.1 hXY hI₁ hI₂' hX'

/-- An end of a surviving occurrence lies over a dictionary image of an abstract
end of its slot. -/
theorem target_mem_absEnds (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (edge : NonDanglingEdge member.data)
    {X : member.data.SourceVertex} (hX : Incident member.data edge.1 X) :
    X.1.1 = absMap member (absEnds m (member.ident.row edge.stablePath)).1 ∨
      X.1.1 = absMap member (absEnds m (member.ident.row edge.stablePath)).2 := by
  have hT := target_eq_slotEdge member hD edge
  have hEnd := target_of_incident member.data edge.1 hX
  rw [hT] at hEnd
  rcases slotEdge_absEnds member hD (member.ident.row edge.stablePath) with h | h <;>
    rw [h] at hEnd <;> rcases hEnd with hEnd | hEnd
  · exact Or.inl hEnd
  · exact Or.inr hEnd
  · exact Or.inr hEnd
  · exact Or.inl hEnd

/-- **Above the branch image of a core vertex carrying no self-loop, the only
surviving source vertex is the branch vertex.** -/
theorem eq_branchVertex_of_surviving (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (c : Fin (4 * m + 2))
    (hc : ∀ t, (catCore m).tail t = (catCore m).head t → (catCore m).tail t ≠ c)
    (X : member.data.SourceVertex) (hX : nonDanglingValency member.data X ≠ 0)
    (hv : X.1.1 = branchImage member c) : X = branchVertex member c := by
  classical
  have hInj := (absMap_bijective member hD).injective
  obtain ⟨edge, hSurvives⟩ : ∃ edge : IncidentSourceEdge member.data X,
      ¬ IsDangling member.data edge.1 := by
    by_contra hNone
    push Not at hNone
    apply hX
    rw [← StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun edge _ hNot ↦ hNot (hNone edge)
  set e : NonDanglingEdge member.data := ⟨edge.1, hSurvives⟩ with he
  set t := member.ident.row e.stablePath with ht
  have hInc : Incident member.data e.1 X := edge.2
  by_cases hLoop : (catCore m).tail t = (catCore m).head t
  · exfalso
    have hEnds : absEnds m t = (Sum.inl ((catCore m).tail t), Sum.inr ⟨t, hLoop⟩) := by
      unfold absEnds; rw [dite_eq_left hLoop]
    have hMem := target_mem_absEnds member hD e hInc
    rw [← ht, hEnds, hv] at hMem
    rcases hMem with h | h
    · have := hInj (show absMap member (Sum.inl c) = _ from h)
      exact hc t hLoop (Sum.inl.inj this).symm
    · have h' : (Sum.inl c : AbsVertex m) = Sum.inr ⟨t, hLoop⟩ :=
        hInj (show absMap member (Sum.inl c) = _ from h)
      exact Sum.inl_ne_inr h'
  · have hNotLeaf : ¬ IsLeafEdge m t := fun hL ↦
      hLoop ((LollipopLeafRow.catCore_tail_eq_head_iff m t).mpr hL)
    rcases incident_of_not_leaf member hD hNotLeaf e ht.symm hInc with h | h
    · have hImg : absMap member (Sum.inl c) = absMap member (Sum.inl ((catCore m).tail t)) := by
        show branchImage member c = branchImage member ((catCore m).tail t)
        rw [← hv, h]; rfl
      rw [h, Sum.inl.inj (hInj hImg)]
    · have hImg : absMap member (Sum.inl c) = absMap member (Sum.inl ((catCore m).head t)) := by
        show branchImage member c = branchImage member ((catCore m).head t)
        rw [← hv, h]; rfl
      rw [h, Sum.inl.inj (hInj hImg)]

/-- **The star shape above a loop-free core vertex**: every sheet off the branch
vertex's block is a single sheet. -/
theorem blockCard_eq_one_off_branch (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (c : Fin (4 * m + 2))
    (hc : ∀ t, (catCore m).tail t = (catCore m).head t → (catCore m).tail t ≠ c)
    (σ : Fin (m + 2))
    (hσ : ¬ (member.data.vertexPartition (branchImage member c)).Rel σ
      (branchVertex member c).1.2) :
    (member.data.vertexPartition (branchImage member c)).blockCard σ = 1 := by
  set X := member.data.sourceEndpoint (branchImage member c) σ with hXdef
  by_cases hZero : nonDanglingValency member.data X = 0
  · have h := blockCard_eq_one_of_nonDanglingValency_eq_zero member X hZero
    rw [← blockCard_congr' _ ((member.data.vertexPartition (branchImage member c)).rel_repr_left σ)]
    exact h
  · exfalso
    have hEq := eq_branchVertex_of_surviving member hD c hc X hZero rfl
    apply hσ
    have h2 := congrArg (fun Z : member.data.SourceVertex ↦ Z.1.2) hEq
    simp only [hXdef, GluingDatum.sourceEndpoint] at h2
    show (member.data.vertexPartition (branchImage member c)).repr σ =
      (member.data.vertexPartition (branchImage member c)).repr (branchVertex member c).1.2
    rw [h2]
    exact ((branchVertex member c).2).symm

/-- **The branch block above an interior spine vertex has size `(a + b + 1)/2`**,
`1/a` and `1/b` being the core diagonal on the two spine slots
(the displayed equation in Part II's proof of `prop-caterpillar-ballot`(1),
`2 m(B) + 1 = a + b + 2`). -/
theorem blockCard_branch_spine (member : FibreMember (catCore m) y (m + 2))
    (hD : member.Diagonal) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * m) :
    ∃ a b : ℕ, member.coreDiag (BallotResidues.spineSlot m i (by omega)) = 1 / (a : ℚ) ∧
      member.coreDiag (BallotResidues.spineSlot m (i + 1) (by omega)) = 1 / (b : ℚ) ∧
      2 * ((member.data.vertexPartition
          (branchImage member (BallotResidues.spineVertex m i hi2))).blockCard
          (branchVertex member (BallotResidues.spineVertex m i hi2)).1.2 : ℤ) + 1 =
        (a : ℤ) + b + 2 := by
  classical
  set c := BallotResidues.spineVertex m i hi2 with hc
  have hInc := BallotResidues.coreIncidence_spineVertex m i hi1 hi2
  have hv1 : (BallotResidues.spineSlot m i (by omega)).val = 3 * i - 2 := rfl
  have hv2 : (BallotResidues.spineSlot m (i + 1) (by omega)).val = 3 * (i + 1) - 2 := rfl
  have hv3 : (BallotResidues.stemSlot m i hi2).val = 3 * i - 1 := rfl
  obtain ⟨e1, hI1, hr1⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member c
    (BallotResidues.spineSlot m i (by omega)) (by rw [hInc, ite_eq_left (by rw [hv1]; omega)]; norm_num)
  obtain ⟨e2, hI2, hr2⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member c
    (BallotResidues.spineSlot m (i + 1) (by omega))
    (by rw [hInc, ite_eq_left (by rw [hv2]; omega)]; norm_num)
  obtain ⟨e3, hI3, hr3⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member c
    (BallotResidues.stemSlot m i hi2) (by rw [hInc, ite_eq_left (by rw [hv3]; omega)]; norm_num)
  set X := (member.ident.vertex.symm c).1 with hX
  have h12 : e1 ≠ e2 := by
    intro h; subst h; have := congrArg Fin.val (hr1.symm.trans hr2); rw [hv1, hv2] at this; omega
  have h13 : e1 ≠ e3 := by
    intro h; subst h; have := congrArg Fin.val (hr1.symm.trans hr3); rw [hv1, hv3] at this; omega
  have h23 : e2 ≠ e3 := by
    intro h; subst h; have := congrArg Fin.val (hr2.symm.trans hr3); rw [hv2, hv3] at this; omega
  have hVal : nonDanglingValency member.data X = 3 :=
    le_antisymm (member.fullDim.trivalent X) (member.ident.vertex.symm c).2
  have hSub : ({e1, e2, e3} : Finset (NonDanglingEdge member.data)) ⊆
      StablePathCount.incidentEdges member.data X := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI1
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI2
    · exact (StablePathCount.mem_incidentEdges _ _ _).mpr hI3
  have hCard3 : ({e1, e2, e3} : Finset (NonDanglingEdge member.data)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hEq : StablePathCount.incidentEdges member.data X = {e1, e2, e3} :=
    (Finset.eq_of_subset_of_card_le hSub
      (by rw [StablePathCount.card_incidentEdges, hVal, hCard3])).symm
  have hStemAdj : BallotOrbit.LoopAdjacent (catCore m) (BallotResidues.stemSlot m i hi2) :=
    (BallotOrbit.loopAdjacent_catCore m _).mpr (by rw [hv3]; omega)
  have hStemLeaf : ¬ IsLeafEdge m (BallotResidues.stemSlot m i hi2) := by
    unfold IsLeafEdge; rw [hv3]; omega
  have h3 := BallotResidues.coreDiag_eq_inv_sourceEdgeIndex member hD e3
    (by rw [hr3]; exact hStemLeaf)
  rw [hr3, LoopAdjacentDiagonal.coreDiag_eq_half_of_loopAdjacent member hD hStemAdj
    hStemLeaf] at h3
  have hIdx3 : member.data.sourceEdgeIndex e3.1 = 2 := by
    have h := inv_injective (by simpa only [one_div] using h3.symm :
      ((member.data.sourceEdgeIndex e3.1 : ℚ))⁻¹ = (2 : ℚ)⁻¹)
    exact_mod_cast h
  have hLeaf1 : ¬ IsLeafEdge m (BallotResidues.spineSlot m i (by omega)) := by
    unfold IsLeafEdge; rw [hv1]; omega
  have hLeaf2 : ¬ IsLeafEdge m (BallotResidues.spineSlot m (i + 1) (by omega)) := by
    unfold IsLeafEdge; rw [hv2]; omega
  have hd1 := BallotResidues.coreDiag_eq_inv_sourceEdgeIndex member hD e1
    (by rw [hr1]; exact hLeaf1)
  have hd2 := BallotResidues.coreDiag_eq_inv_sourceEdgeIndex member hD e2
    (by rw [hr2]; exact hLeaf2)
  rw [hr1] at hd1
  rw [hr2] at hd2
  refine ⟨member.data.sourceEdgeIndex e1.1, member.data.sourceEdgeIndex e2.1, hd1, hd2, ?_⟩
  have hNe : ∀ (slot : Fin (6 * m + 3))
      (hLoop : (catCore m).tail slot = (catCore m).head slot),
      X ≠ LollipopDivalent.loopBranch member hLoop := by
    intro slot hLoop hXeq
    have h' : member.ident.vertex.symm c = member.ident.vertex.symm ((catCore m).tail slot) :=
      Subtype.ext hXeq
    exact BallotResidues.tail_ne_spineVertex_of_loop m i hi1 hi2 hLoop
      (member.ident.vertex.symm.injective h').symm
  have hTri := BranchSharedDirection.incidentEdges_card_eq_three_of_branch_of_ne member hVal hNe
  have hZero := SlopesGeometric.localRamification_eq_zero_of_trivalent_target member.data
    member.fullDim.valid X.1.1 (member.fullDim.changeMinimal _) hTri ⟨X.1.2, X.2⟩
  have hSum := SlopesGeometric.survivingIndexSum_of_trivalent_unramified member.data
    member.fullDim.danglingEdgeNoGlue X hVal hZero
  rw [BallotResidues.survivingIndexSum_eq_sum_incidentEdges, hEq,
    Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23, hIdx3] at hSum
  have hgoal : (member.data.vertexPartition (branchImage member c)).blockCard
      (branchVertex member c).1.2 =
      (member.data.vertexPartition X.1.1).blockCard X.1.2 := rfl
  rw [hgoal]
  push_cast at hSum
  linarith

/-- **The per-vertex census, at every interior spine vertex.**  Two
diagonal members with the same core diagonal carry, above corresponding interior
spine vertices (corresponding under Half 1's target layer), partitions that are
relabellings of each other.  No request, openness or oddness is used. -/
theorem spine_vertexPartition_relabel (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hDiag : mem₁.coreDiag = mem₂.coreDiag) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ 2 * m) :
    ∃ π : Equiv.Perm (Fin (m + 2)),
      mem₂.data.vertexPartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex
          (branchImage mem₁ (BallotResidues.spineVertex m i hi2))) =
        (mem₁.data.vertexPartition
          (branchImage mem₁ (BallotResidues.spineVertex m i hi2))).relabel π := by
  have hLoopFree : ∀ t, (catCore m).tail t = (catCore m).head t →
      (catCore m).tail t ≠ BallotResidues.spineVertex m i hi2 :=
    fun t hLoop ↦ BallotResidues.tail_ne_spineVertex_of_loop m i hi1 hi2 hLoop
  rw [targetLayer_branchImage]
  obtain ⟨a₁, b₁, ha₁, hb₁, h₁⟩ := blockCard_branch_spine mem₁ hD₁ i hi1 hi2
  obtain ⟨a₂, b₂, ha₂, hb₂, h₂⟩ := blockCard_branch_spine mem₂ hD₂ i hi1 hi2
  rw [hDiag] at ha₁ hb₁
  have ha : (a₁ : ℚ) = a₂ := by
    have := ha₁.symm.trans ha₂
    simpa only [one_div, inv_inj] using this
  have hb : (b₁ : ℚ) = b₂ := by
    have := hb₁.symm.trans hb₂
    simpa only [one_div, inv_inj] using this
  have ha' : a₁ = a₂ := by exact_mod_cast ha
  have hb' : b₁ = b₂ := by exact_mod_cast hb
  subst ha' hb'
  exact exists_relabel_of_star _ _ _ _ (by omega)
    (blockCard_eq_one_off_branch mem₁ hD₁ _ hLoopFree)
    (blockCard_eq_one_off_branch mem₂ hD₂ _ hLoopFree)

end SpineCensus

/-! ## 6.  The obligation, its consumer, and the pilot -/

section Obligation

open BallotCoreIdentification (ballotFamilyMember)

/-- **The sheet-layer supply** (the label-respecting form of `hSupply`).  For
every slope sequence `s` and every open odd diagonal member whose core diagonal
is the ballot diagonal of `s`, there is a sheet layer between the ballot datum at
`s` and the member's datum **over the target layer of Half 1**.

It implies `hSupply` (`hSupply_of_sheetLayerSupply`); the converse would need uniqueness
of the target layer, which is not proved here.  It is proved in `SheetLayerMatching`. -/
def SheetLayerSupply (m : ℕ) (request : Fin (6 * m + 3) → ℚ) : Prop :=
  ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
    mem.Open → mem.HasOddMult → ∀ hD : mem.Diagonal,
      mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
        Nonempty (SheetLayer (ballotFamilyMember m request s).data mem.data
          (targetLayer (ballotFamilyMember m request s) mem
            (RigidityBasepoint.ballotFamilyMember_diagonal m request s) hD))

/-- **The implication to `hSupply`**, in the exact binder shape of
`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`
(at every `m`; genus six is `m = 2`). -/
theorem hSupply_of_sheetLayerSupply {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (h : SheetLayerSupply m request) :
    ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
          Nonempty (GeometricDatumIso (ballotFamilyMember m request s).data mem.data) := by
  intro s mem hOpen hOdd hD hDiag
  obtain ⟨sheets⟩ := h s mem hOpen hOdd hD hDiag
  exact ⟨sheets.toIso⟩

/-- **The pilot: the sheet layer between a ballot member and itself**, at every
`s` (in particular at `s = zig`), over the Half-1 target layer -- which is the
identity pointwise, so the identity permutations serve. -/
theorem sheetLayer_ballot_self (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) :
    Nonempty (SheetLayer (ballotFamilyMember m request s).data
      (ballotFamilyMember m request s).data
      (targetLayer (ballotFamilyMember m request s) (ballotFamilyMember m request s)
        (RigidityBasepoint.ballotFamilyMember_diagonal m request s)
        (RigidityBasepoint.ballotFamilyMember_diagonal m request s))) :=
  ⟨SheetLayer.ofId _ _ (targetLayer_self_vertex _ _) (targetLayer_self_edge _ _)⟩

/-- The pilot at the zig-zag. -/
theorem sheetLayer_ballot_zig (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    Nonempty (SheetLayer (ballotFamilyMember m request (BallotDatum.zig m)).data
      (ballotFamilyMember m request (BallotDatum.zig m)).data
      (targetLayer (ballotFamilyMember m request (BallotDatum.zig m))
        (ballotFamilyMember m request (BallotDatum.zig m))
        (RigidityBasepoint.ballotFamilyMember_diagonal m request _)
        (RigidityBasepoint.ballotFamilyMember_diagonal m request _))) :=
  sheetLayer_ballot_self m request _

/-- The antecedent of `SheetLayerSupply` is inhabited at every positive request:
the ballot member at `s` is open, odd, diagonal, and reads the ballot diagonal of
`s`. -/
example {m : ℕ} {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (s : Slopes (2 * (m + 1))) :
    ∃ mem : FibreMember (catCore m) request (m + 2),
      mem.Open ∧ mem.HasOddMult ∧ mem.Diagonal ∧
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s :=
  ⟨ballotFamilyMember m request s, BallotCoreIdentification.ballotFamilyMember_open m hRequest s,
    BallotCoreIdentification.ballotFamilyMember_hasOddMult m request s,
    RigidityBasepoint.ballotFamilyMember_diagonal m request s,
    RigidityBasepoint.ballotFamilyMember_coreDiag m request s⟩

/-! ### The pilot at the caterpillar member

`BallotResidues.supply_caterpillarMember` is `hSupply` at the caterpillar member,
where the only `s` is the zig-zag and the iso is the identity.  The obligation
here is *stronger* than `hSupply` -- its target maps are pinned to Half 1's -- so
it is tested at the same member: Half 1's target layer between the zig-zag ballot
member and the caterpillar member is the identity of `catTree m`, pointwise, and
the two data are equal (`BallotDatum.ballotDatum_zig`). -/

section Caterpillar

open DraismaVargas.Infrastructure.CaterpillarTree

variable (m : ℕ) (request : Fin (6 * m + 3) → ℚ)

theorem slotEdge_ballotFamilyMember (s : Slopes (2 * (m + 1))) (t : Fin (6 * m + 3)) :
    slotEdge (ballotFamilyMember m request s) t = catEdgeEquiv m t := by
  have h : (ballotFamilyMember m request s).slotMap.symm t = t := by
    rw [Equiv.symm_apply_eq, BallotCoreIdentification.ballotFamilyMember_slotMap]
  rw [slotEdge, Equiv.trans_apply, h]
  rfl

theorem slotEdge_caterpillarMember (t : Fin (6 * m + 3)) :
    slotEdge (caterpillarMember m request) t = catEdgeEquiv m t := by
  rw [slotEdge, Equiv.trans_apply, slotMap_symm_caterpillarMember]
  rfl

theorem branchImage_ballotFamilyMember (s : Slopes (2 * (m + 1))) (c : Fin (4 * m + 2)) :
    branchImage (ballotFamilyMember m request s) c = branchVertexOf m c := rfl

theorem branchImage_caterpillarMember (c : Fin (4 * m + 2)) :
    branchImage (caterpillarMember m request) c = branchVertexOf m c := rfl

theorem absMap_ballot_eq_caterpillar (s : Slopes (2 * (m + 1))) (x : AbsVertex m) :
    absMap (ballotFamilyMember m request s) x = absMap (caterpillarMember m request) x := by
  rcases x with c | t
  · rfl
  · show tip (ballotFamilyMember m request s) t.1 = tip (caterpillarMember m request) t.1
    unfold tip
    rw [slotEdge_ballotFamilyMember, slotEdge_caterpillarMember,
      branchImage_ballotFamilyMember, branchImage_caterpillarMember]
    split_ifs <;> first | rfl | contradiction

/-- **Half 1's target layer between the zig-zag ballot member and the caterpillar
member is the identity of `catTree m`**, on vertices ... -/
theorem targetLayer_ballot_caterpillar_vertex (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    (targetLayer (ballotFamilyMember m request s) (caterpillarMember m request)
      (RigidityBasepoint.ballotFamilyMember_diagonal m request s)
      (diagonal_caterpillarMember m request)).targetVertex v = v := by
  set ψ := absEquiv (ballotFamilyMember m request s)
    (RigidityBasepoint.ballotFamilyMember_diagonal m request s)
  show absMap (caterpillarMember m request) (ψ.symm v) = v
  rw [← absMap_ballot_eq_caterpillar m request s]
  exact ψ.apply_symm_apply v

/-- ... and on edges. -/
theorem targetLayer_ballot_caterpillar_edge (s : Slopes (2 * (m + 1)))
    (e : (catTree m).edges) :
    (targetLayer (ballotFamilyMember m request s) (caterpillarMember m request)
      (RigidityBasepoint.ballotFamilyMember_diagonal m request s)
      (diagonal_caterpillarMember m request)).targetEdge e = e := by
  obtain ⟨t, rfl⟩ := (slotEdge (ballotFamilyMember m request s)).surjective e
  rw [targetLayer_slotEdge, slotEdge_caterpillarMember, slotEdge_ballotFamilyMember]

/-- **The obligation holds at the caterpillar member**: the sheet layer exists
over Half 1's target layer (not merely over *some* target layer, which is what
`BallotResidues.supply_caterpillarMember` gives). -/
theorem sheetLayer_caterpillarMember (s : Slopes (2 * (m + 1)))
    (hs : (caterpillarMember m request).coreDiag = BallotSlopes.ballotCoreDiag m s) :
    Nonempty (SheetLayer (ballotFamilyMember m request s).data
      (caterpillarMember m request).data
      (targetLayer (ballotFamilyMember m request s) (caterpillarMember m request)
        (RigidityBasepoint.ballotFamilyMember_diagonal m request s)
        (diagonal_caterpillarMember m request))) := by
  have hzig : s = BallotDatum.zig m :=
    BallotSlopes.ballotCoreDiag_injective m
      (hs.symm.trans (BallotSlopes.coreDiag_caterpillarMember_eq_zig m request))
  subst hzig
  have hData : (ballotFamilyMember m request (BallotDatum.zig m)).data =
      (caterpillarMember m request).data := BallotDatum.ballotDatum_zig m
  refine ⟨⟨fun _ ↦ Equiv.refl _, fun _ ↦ Equiv.refl _, ?_, ?_, fun _ _ _ _ ↦ rfl⟩⟩
  · intro v
    erw [targetLayer_ballot_caterpillar_vertex]
    rw [← hData]
    exact (Transport.DatumIso.refl _).vertexPartition v
  · intro e
    erw [targetLayer_ballot_caterpillar_edge]
    rw [← hData]
    exact (Transport.DatumIso.refl _).edgePartition e

end Caterpillar

end Obligation

/-! ## 7.  A per-piece partition census does not determine the sheet layer

One might expect the sheet layer to factor vertex by vertex: the partition at each
target vertex is forced up to a permutation, and `compatible` is local, so Half 2 would
be a per-vertex census.  The first half holds for diagonal members (§5), but the
conclusion does not: the permutations are coupled along every edge by `compatible`, and
matching censuses at every vertex and every edge do not give a `GeometricDatumIso`.  The
witness is over the three-vertex path `TargetNormalForm.inPath`, at degree three: every vertex
and edge partition of `pathTree` is a relabelling of the corresponding one of
`pathCycle` (the same target piece), `pathTree` is a valid gluing datum, and there
is no `GeometricDatumIso pathTree pathCycle` at all -- because the source of
`pathTree` is connected (a path) and that of `pathCycle` is not (a 4-cycle and a
path).  Which sheets meet which is global data. -/

section Census

open TargetNormalForm (inPath)

/-- Blocks `{0}` and `{1, 2}`. -/
def partZero : SheetPartition 3 where
  repr := fun sheet ↦ if sheet = 0 then 0 else 1
  repr_idem := by decide

/-- Blocks `{1}` and `{0, 2}`. -/
def partOne : SheetPartition 3 where
  repr := fun sheet ↦ if sheet = 1 then 1 else 0
  repr_idem := by decide

/-- The middle vertex of the path. -/
def midV : inPath.V := show Fin 3 from 1

/-- The leaf stored first by the first occurrence. -/
def leftV : inPath.V := show Fin 3 from 0

/-- `{0} {1,2}` at both leaves, discrete at the middle and on both occurrences:
sheets `1` and `2` close up into a 4-cycle, sheet `0` is a separate path. -/
def pathCycle : GluingDatum inPath 3 where
  degree_pos := by decide
  vertexPartition v := if v = midV then SheetPartition.discrete 3 else partZero
  edgePartition _ := SheetPartition.discrete 3
  refines_left _ := SheetPartition.discrete_refines _
  refines_right _ := SheetPartition.discrete_refines _

/-- As `pathCycle`, except `{1} {0,2}` at the leaf `2`: the source is a path. -/
def pathTree : GluingDatum inPath 3 where
  degree_pos := by decide
  vertexPartition v :=
    if v = midV then SheetPartition.discrete 3
    else if v = leftV then partZero else partOne
  edgePartition _ := SheetPartition.discrete 3
  refines_left _ := SheetPartition.discrete_refines _
  refines_right _ := SheetPartition.discrete_refines _

theorem pathTree_valid : pathTree.Valid :=
  ⟨(GluingDatum.checkConnected_eq_true_iff pathTree).mp (by decide +kernel),
    (GluingDatum.checkRiemannHurwitz_eq_true_iff pathTree).mp (by decide +kernel)⟩

theorem not_pathCycle_connected : ¬ pathCycle.Connected := by
  rw [← GluingDatum.checkConnected_eq_true_iff]
  decide +kernel

theorem partOne_eq_relabel : partOne = partZero.relabel (Equiv.swap 0 1) := by
  apply SheetPartition.ext_repr
  funext sheet
  revert sheet
  decide

/-- **The census matches at every target piece**, over the identity of the target. -/
theorem pathTree_vertexCensus (v : inPath.V) :
    ∃ π : Equiv.Perm (Fin 3),
      pathTree.vertexPartition v = (pathCycle.vertexPartition v).relabel π := by
  by_cases h1 : v = midV
  · refine ⟨Equiv.refl _, ?_⟩
    simp only [pathTree, pathCycle, ite_eq_left h1]
    exact (Transport.DatumIso.relabel_refl _).symm
  · by_cases h0 : v = leftV
    · refine ⟨Equiv.refl _, ?_⟩
      simp only [pathTree, pathCycle, ite_eq_right h1, ite_eq_left h0]
      exact (Transport.DatumIso.relabel_refl _).symm
    · refine ⟨Equiv.swap 0 1, ?_⟩
      simp only [pathTree, pathCycle, ite_eq_right h1, ite_eq_right h0]
      exact partOne_eq_relabel

theorem pathTree_edgeCensus (e : inPath.edges) :
    ∃ π : Equiv.Perm (Fin 3),
      pathTree.edgePartition e = (pathCycle.edgePartition e).relabel π :=
  ⟨Equiv.refl _, (Transport.DatumIso.relabel_refl _).symm⟩

/-- **A per-piece census is not sufficient.**  Matching partitions at every target
vertex and every target occurrence (even over the identity of the target), with
the first datum valid, do not give a `GeometricDatumIso`. -/
theorem census_not_sufficient :
    ∃ first second : GluingDatum inPath 3, first.Valid ∧
      (∀ v, ∃ π : Equiv.Perm (Fin 3),
        first.vertexPartition v = (second.vertexPartition v).relabel π) ∧
      (∀ e, ∃ π : Equiv.Perm (Fin 3),
        first.edgePartition e = (second.edgePartition e).relabel π) ∧
      IsEmpty (GeometricDatumIso first second) :=
  ⟨pathTree, pathCycle, pathTree_valid, pathTree_vertexCensus, pathTree_edgeCensus,
    ⟨fun iso ↦ not_pathCycle_connected (iso.connected pathTree_valid.1)⟩⟩

end Census

end DraismaVargas.Count.DiagonalTargetIso
