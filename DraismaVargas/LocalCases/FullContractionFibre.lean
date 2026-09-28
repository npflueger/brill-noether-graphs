import DraismaVargas.LocalCases.PrunedFibreValency

/-!
# The literal full fibre count of a forest contraction

Source: Draisma–Vargas Part I, arXiv:1909.12924, Proposition `prop-rphi-under-contraction`
(`r_φ` under contraction), whose proof shows that the subgraph contracting to
`A_0` is a tree, and the corresponding statement for its non-dangling part
(subsection `subsection-the-graph-GqA0`).
`ContractionForest` is the equality between numbers of fine partition blocks.
Here those exact blocks are counted as actual source vertices and actual
source-edge occurrences of one fibre.
-/

namespace DraismaVargas.LocalCases.FullContractionFibre

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource StableLocalProperties PrunedFibreValency

variable {target : CFGraph} {degree : ℕ}

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The actual merged source vertex named by a block of the join partition. -/
noncomputable def mergedVertex (block : (mergedPartition data a b).Blocks) :
    (contractDatum data hc hab hOne).SourceVertex :=
  ⟨(⟨a, hab⟩, block.1), by
    change ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr block.1 = block.1
    rw [contractDatum_vertexPartition_merge]
    exact block.2⟩

/-- Membership in the actual fibre is precisely lying over an endpoint and
having the specified join-block representative. -/
theorem mem_fibreVertices_mergedVertex_iff
    (block : (mergedPartition data a b).Blocks) (first : data.SourceVertex) :
    first ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) ↔
      (first.1.1 = a ∨ first.1.1 = b) ∧
        (mergedPartition data a b).repr first.1.2 = block.1 := by
  rw [mem_fibreVertices]
  constructor
  · intro h
    have hTarget := congrArg
      (fun vertex : (contractDatum data hc hab hOne).SourceVertex ↦ vertex.1.1) h
    have hSheet := congrArg
      (fun vertex : (contractDatum data hc hab hOne).SourceVertex ↦ vertex.1.2) h
    change fold target hab first.1.1 = ⟨a, hab⟩ at hTarget
    have hEnds : first.1.1 = a ∨ first.1.1 = b := by
      simpa only [fold_eq_iff, true_and] using hTarget
    refine ⟨hEnds, ?_⟩
    change (contractVertexPartition data a b (fold target hab first.1.1)).repr first.1.2 =
      block.1 at hSheet
    rw [contractVertexPartition_fold_merge data hab hEnds] at hSheet
    exact hSheet
  · rintro ⟨hEnds, hSheet⟩
    apply Subtype.ext
    apply Prod.ext
    · exact (fold_eq_iff target hab first.1.1 ⟨a, hab⟩).mpr
        (hEnds.imp_right fun h ↦ ⟨rfl, h⟩)
    · change (contractVertexPartition data a b (fold target hab first.1.1)).repr first.1.2 =
        block.1
      rw [contractVertexPartition_fold_merge data hab hEnds]
      exact hSheet

/-- Literal source vertices over one target endpoint lying in a join block. -/
noncomputable def sideVertices (side : target.V)
    (block : (mergedPartition data a b).Blocks) : Finset data.SourceVertex :=
  (SheetPartition.blocksWithin (data.vertexPartition side)
    (mergedPartition data a b) block).image (blockVertex data side)

theorem mem_sideVertices_iff (side : target.V)
    (block : (mergedPartition data a b).Blocks) (first : data.SourceVertex) :
    first ∈ sideVertices data (a := a) (b := b) side block ↔
      first.1.1 = side ∧ (mergedPartition data a b).repr first.1.2 = block.1 := by
  classical
  simp only [sideVertices, Finset.mem_image]
  constructor
  · rintro ⟨fine, hFine, rfl⟩
    refine ⟨rfl, ?_⟩
    have hMap := (SheetPartition.mem_blocksWithin _ _ _ _).mp hFine
    exact congrArg Subtype.val hMap
  · rintro ⟨hSide, hRepr⟩
    let fine : (data.vertexPartition side).Blocks := ⟨first.1.2, by
      rw [← hSide]
      exact first.2⟩
    refine ⟨fine, (SheetPartition.mem_blocksWithin _ _ _ _).mpr ?_, ?_⟩
    · exact Subtype.ext hRepr
    · exact Subtype.ext (Prod.ext hSide.symm rfl)

theorem sideVertices_card (side : target.V)
    (block : (mergedPartition data a b).Blocks) :
    (sideVertices data (a := a) (b := b) side block).card =
      (SheetPartition.blocksWithin (data.vertexPartition side)
        (mergedPartition data a b) block).card := by
  classical
  apply Finset.card_image_of_injective
  intro first second h
  exact Subtype.ext (congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) h)

/-- The full source fibre is the disjoint union of the actual fine blocks
over the two endpoints of the contracted target occurrence. -/
theorem fibreVertices_mergedVertex
    (block : (mergedPartition data a b).Blocks) :
    fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
      sideVertices data a block ∪ sideVertices data b block := by
  classical
  ext first
  rw [mem_fibreVertices_mergedVertex_iff, Finset.mem_union,
    mem_sideVertices_iff, mem_sideVertices_iff]
  exact or_and_right

theorem sideVertices_disjoint (hApart : a ≠ b) (block : (mergedPartition data a b).Blocks) :
    Disjoint (sideVertices data a block) (sideVertices data b block) := by
  classical
  apply Finset.disjoint_left.mpr
  intro first hFirst hSecond
  exact hApart (((mem_sideVertices_iff data a block first).mp hFirst).1.symm.trans
    ((mem_sideVertices_iff data b block first).mp hSecond).1)

/-- The vertex half of the actual full-fibre Euler census. -/
theorem fibreVertices_mergedVertex_card
    (block : (mergedPartition data a b).Blocks) :
    (fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).card =
      (SheetPartition.blocksWithin (data.vertexPartition a) (mergedPartition data a b) block).card +
        (SheetPartition.blocksWithin (data.vertexPartition b) (mergedPartition data a b) block).card := by
  rw [fibreVertices_mergedVertex, Finset.card_union_of_disjoint
    (sideVertices_disjoint data hab block), sideVertices_card, sideVertices_card]

/-- The actual source occurrence associated to one fixed block over the
contracted target occurrence. -/
def edgeOfBlock (edge : target.edges) (block : (data.edgePartition edge).Blocks) :
    data.SourceEdge := ⟨(edge, block.1), block.2⟩

/-- Literal internal source occurrences in a join block, before pruning. -/
noncomputable def fullInternalEdges (edge : target.edges)
    (block : (mergedPartition data a b).Blocks) : Finset data.SourceEdge :=
  (SheetPartition.blocksWithin (data.edgePartition edge)
    (mergedPartition data a b) block).image (edgeOfBlock data edge)

theorem mem_fullInternalEdges_iff (edge : target.edges)
    (block : (mergedPartition data a b).Blocks) (first : data.SourceEdge) :
    first ∈ fullInternalEdges data (a := a) (b := b) edge block ↔
      first.1.1 = edge ∧ (mergedPartition data a b).repr first.1.2 = block.1 := by
  classical
  simp only [fullInternalEdges, Finset.mem_image]
  constructor
  · rintro ⟨fine, hFine, rfl⟩
    refine ⟨rfl, ?_⟩
    exact congrArg Subtype.val ((SheetPartition.mem_blocksWithin _ _ _ _).mp hFine)
  · rintro ⟨hTarget, hRepr⟩
    let fine : (data.edgePartition edge).Blocks := ⟨first.1.2, by
      rw [← hTarget]
      exact first.2⟩
    refine ⟨fine, (SheetPartition.mem_blocksWithin _ _ _ _).mpr ?_, ?_⟩
    · exact Subtype.ext hRepr
    · exact Subtype.ext (Prod.ext hTarget.symm rfl)

theorem fullInternalEdges_card (edge : target.edges)
    (block : (mergedPartition data a b).Blocks) :
    (fullInternalEdges data (a := a) (b := b) edge block).card =
      (SheetPartition.blocksWithin (data.edgePartition edge)
        (mergedPartition data a b) block).card := by
  classical
  apply Finset.card_image_of_injective
  intro first second h
  exact Subtype.ext (congrArg (fun edge : data.SourceEdge ↦ edge.1.2) h)

/-- The occurrence half of the actual full-fibre Euler census.  This is an
equivalence on literal occurrences, so parallel occurrences are not collapsed. -/
theorem sourceEnds_mem_fibre_mergedVertex_iff
    (block : (mergedPartition data a b).Blocks) (edge : data.SourceEdge) :
    ((data.sourceEnds edge).1 ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) ∧
      (data.sourceEnds edge).2 ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)) ↔
      edge ∈ fullInternalEdges data contracted block := by
  rw [mem_fullInternalEdges_iff]
  have hTargetFacts (hTarget : edge.1.1 = contracted) :
      ((edge.1.1 : target.V × target.V).1 = a) ∧
        ((edge.1.1 : target.V × target.V).2 = b) := by
    rw [hTarget, hc]
    exact ⟨rfl, rfl⟩
  constructor
  · rintro ⟨hFirst, hSecond⟩
    have hTarget : edge.1.1 = contracted := by
      by_contra hNe
      exact sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨edge, hNe⟩
        (((mem_fibreVertices data hc hab hOne _ _).mp hFirst).trans
          ((mem_fibreVertices data hc hab hOne _ _).mp hSecond).symm)
    refine ⟨hTarget, ?_⟩
    have hSheet := ((mem_fibreVertices_mergedVertex_iff data hc hab hOne block _).mp hFirst).2
    have hFirstSheet : (data.sourceEnds edge).1.1.2 =
        (data.vertexPartition a).repr edge.1.2 := by
      change (data.vertexPartition (edge.1.1 : target.V × target.V).1).repr edge.1.2 = _
      rw [(hTargetFacts hTarget).1]
    rw [hFirstSheet] at hSheet
    have hRefines := (vertexPartition_refines_mergedPartition data a b).rel
      ((data.vertexPartition a).rel_repr_left edge.1.2)
    exact hRefines.symm.trans hSheet
  · rintro ⟨hTarget, hSheet⟩
    have hFacts := hTargetFacts hTarget
    rw [mem_fibreVertices_mergedVertex_iff, mem_fibreVertices_mergedVertex_iff]
    constructor
    · refine ⟨Or.inl hFacts.1, ?_⟩
      change (mergedPartition data a b).repr
        ((data.vertexPartition (edge.1.1 : target.V × target.V).1).repr edge.1.2) = _
      rw [hFacts.1]
      exact ((vertexPartition_refines_mergedPartition data a b).rel
        ((data.vertexPartition a).rel_repr_left edge.1.2)).trans hSheet
    · refine ⟨Or.inr hFacts.2, ?_⟩
      change (mergedPartition data a b).repr
        ((data.vertexPartition (edge.1.1 : target.V × target.V).2).repr edge.1.2) = _
      rw [hFacts.2]
      exact ((vertexPartition_refines_mergedPartition_right data a b).rel
        ((data.vertexPartition b).rel_repr_left edge.1.2)).trans hSheet

/-- The partition forest equality `ContractionForest`, read on actual
occurrences and actual source vertices in the full contraction fibre. -/
theorem fullInternalEdges_card_add_one_eq_fibreVertices_card
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks) :
    (fullInternalEdges data contracted block).card + 1 =
      (fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).card := by
  rw [fullInternalEdges_card, fibreVertices_mergedVertex_card]
  exact hForest block

end Fibre

end DraismaVargas.LocalCases.FullContractionFibre
