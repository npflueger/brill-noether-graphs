module

public import DraismaVargas.LocalCases.ResolutionCut
public import DraismaVargas.LocalCases.ZeroForestBridge

@[expose] public section

/-!
# Euler counts restricted to a union of source-contraction fibres

The whole-source Euler formula is not enough to descend a dangling side.
We count only the old wall blocks selected by that side. The existing local
join inequality `L + R ≤ E + 1` remains valid after summing over any such
selection; no forest premise is needed for the downward genus inequality.
-/

namespace DraismaVargas.LocalCases.ResolutionSideCounts

open DraismaVargas.Infrastructure
open SheetPartition ResolutionM11 GlobalResolution TargetExpansion

variable {degree : ℕ}

noncomputable local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Fine blocks whose containing coarse block lies in the selected set. -/
noncomputable def selectedBlocks (fine coarse : SheetPartition degree)
    (selected : Finset coarse.Blocks) : Finset fine.Blocks := by
  exact Finset.univ.filter fun block ↦ fineBlockToCoarseBlock fine coarse block ∈ selected

theorem card_selectedBlocks (fine coarse : SheetPartition degree)
    (hRefines : fine.Refines coarse) (selected : Finset coarse.Blocks) :
    (selectedBlocks fine coarse selected).card =
      ∑ block ∈ selected, fine.blockCountWithin coarse block.1 := by
  calc
    _ = ∑ block ∈ selected, (blocksWithin fine coarse block).card :=
      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ selected
        (fineBlockToCoarseBlock fine coarse)).symm
    _ = _ := Finset.sum_congr rfl fun block _ ↦
      card_blocksWithin_eq_blockCountWithin fine coarse hRefines block

/-- The connected-fibre Euler inequality holds on any selected wall blocks,
not just after summing over the whole source. -/
theorem selected_euler_le (coarse : SheetPartition degree) (resolution : LocalResolution degree)
    (hContracts : resolution.ContractsTo coarse) (selected : Finset coarse.Blocks) :
    (selectedBlocks resolution.left coarse selected).card +
        (selectedBlocks resolution.right coarse selected).card ≤
      (selectedBlocks resolution.newEdge coarse selected).card + selected.card := by
  have hSame : (SheetPartition.join resolution.left resolution.right).SameBlocks coarse :=
    fun first second ↦ (SheetPartition.join_rel_iff _ _ first second).trans (hContracts first second).symm
  have hLocal (block : coarse.Blocks) :
      resolution.left.blockCountWithin coarse block.1 +
          resolution.right.blockCountWithin coarse block.1 ≤
        resolution.newEdge.blockCountWithin coarse block.1 + 1 := by
    have h := ZeroForestBridge.blockCountWithin_join_add_le
      resolution.edge_refines_left resolution.edge_refines_right block.1
    simpa only [hSame.blockCountWithin_eq_coarse] using h
  rw [card_selectedBlocks _ _ hContracts.left_refines,
    card_selectedBlocks _ _ hContracts.right_refines,
    card_selectedBlocks _ _ (resolution.edge_refines_left.trans hContracts.left_refines)]
  have hSum := Finset.sum_le_sum (s := selected) (fun block _ ↦ hLocal block)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] using hSum

/-- Selected and unselected coarse blocks partition every fine-block census. -/
theorem card_selectedBlocks_add_complement (fine coarse : SheetPartition degree)
    (selected : Finset coarse.Blocks) :
    (selectedBlocks fine coarse selected).card +
        (selectedBlocks fine coarse (Finset.univ \ selected)).card = Fintype.card fine.Blocks := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset fine.Blocks))
    (p := fun block ↦ fineBlockToCoarseBlock fine coarse block ∈ selected)
  simpa [selectedBlocks] using h

/-- If the whole connected-fibre Euler defect is zero, its nonnegative
defect on any selected blocks is zero as well. -/
theorem selected_euler_eq (coarse : SheetPartition degree) (resolution : LocalResolution degree)
    (hContracts : resolution.ContractsTo coarse)
    (hTotal : Fintype.card resolution.newEdge.Blocks + Fintype.card coarse.Blocks =
      Fintype.card resolution.left.Blocks + Fintype.card resolution.right.Blocks)
    (selected : Finset coarse.Blocks) :
    (selectedBlocks resolution.left coarse selected).card +
        (selectedBlocks resolution.right coarse selected).card =
      (selectedBlocks resolution.newEdge coarse selected).card + selected.card := by
  have hSelected := selected_euler_le coarse resolution hContracts selected
  have hComplement := selected_euler_le coarse resolution hContracts (Finset.univ \ selected)
  have hLeft := card_selectedBlocks_add_complement resolution.left coarse selected
  have hRight := card_selectedBlocks_add_complement resolution.right coarse selected
  have hEdge := card_selectedBlocks_add_complement resolution.newEdge coarse selected
  have hCoarse : (Finset.univ \ selected).card + selected.card = Fintype.card coarse.Blocks := by
    simpa only [Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ selected)
  omega

/-- Count canonical blocks using a predicate on their representative sheets. -/
noncomputable def blockCount (partition : SheetPartition degree)
    (predicate : Fin degree → Prop) : ℕ := by
  exact (Finset.univ.filter fun block : partition.Blocks ↦ predicate block.1).card

/-- Counting selected source vertices can be performed target vertex by
target vertex, using their actual canonical partition blocks. -/
theorem card_filter_sourceVertex (target : CFGraph) (data : GluingDatum target degree)
    (predicate : data.SourceVertex → Prop) :
    (Finset.univ.filter predicate).card =
      ∑ vertex : target.V,
        blockCount (data.vertexPartition vertex)
          (fun sheet ↦ predicate (data.sourceEndpoint vertex sheet)) := by
  simp only [Finset.card_filter, blockCount]
  trans ∑ pair : (Σ vertex : target.V, (data.vertexPartition vertex).Blocks),
    if predicate (data.sourceEndpoint pair.1 pair.2.1) then 1 else 0
  · apply Fintype.sum_equiv data.sourceVertexEquivSigmaBlocks
    intro vertex
    change (if predicate vertex then 1 else 0) =
      if predicate (data.sourceEndpoint vertex.1.1 vertex.1.2) then 1 else 0
    rw [data.sourceEndpoint_self]
  · exact Fintype.sum_sigma _

/-- The same occurrence-safe census for selected source edges. -/
theorem card_filter_sourceEdge (target : CFGraph) (data : GluingDatum target degree)
    (predicate : data.SourceEdge → Prop) :
    (Finset.univ.filter predicate).card =
      ∑ edge : target.edges,
        blockCount (data.edgePartition edge)
          (fun sheet ↦ predicate (data.sourceEdge edge sheet)) := by
  simp only [Finset.card_filter, blockCount]
  trans ∑ pair : (Σ edge : target.edges, (data.edgePartition edge).Blocks),
    if predicate (data.sourceEdge pair.1 pair.2.1) then 1 else 0
  · apply Fintype.sum_equiv data.sourceEdgeEquivSigmaBlocks
    intro edge
    change (if predicate edge then 1 else 0) =
      if predicate (data.sourceEdge edge.1.1 edge.1.2) then 1 else 0
    rw [W4StableSource.GluingDatum.sourceEdge_self]
  · exact Fintype.sum_sigma _

variable {target : CFGraph}

/-- The old wall blocks selected by a vertex side of the old source. -/
noncomputable def selectedWall (data : GluingDatum target degree) (wall : target.V)
    (side : Finset data.SourceVertex) : Finset (data.vertexPartition wall).Blocks := by
  exact Finset.univ.filter fun block ↦ data.sourceEndpoint wall block.1 ∈ side

/-- Selection through a coarse canonical block is the same as selection
through any of its sheets. -/
theorem blockCount_eq_selectedBlocks (data : GluingDatum target degree) (wall : target.V)
    (side : Finset data.SourceVertex) (fine : SheetPartition degree) :
    blockCount fine (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) =
      (selectedBlocks fine (data.vertexPartition wall) (selectedWall data wall side)).card := by
  have hEndpoint (sheet : Fin degree) :
      data.sourceEndpoint wall ((data.vertexPartition wall).repr sheet) = data.sourceEndpoint wall sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (data.vertexPartition wall).repr_idem sheet
  unfold blockCount
  congr 1
  ext block
  simp only [selectedBlocks, selectedWall, Finset.mem_filter, Finset.mem_univ, true_and,
    fineBlockToCoarseBlock, SheetPartition.toBlock_val, hEndpoint]

theorem blockCount_wall (data : GluingDatum target degree) (wall : target.V)
    (side : Finset data.SourceVertex) :
    blockCount (data.vertexPartition wall) (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) =
      (selectedWall data wall side).card := by
  unfold blockCount selectedWall
  congr 1
  ext block
  simp

/-- The complete preimage of an old source side under a literal resolution. -/
noncomputable def preimageSide (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (side : Finset data.SourceVertex) : Finset (datum data wall right resolution hCompatible).SourceVertex := by
  exact Finset.univ.filter fun vertex ↦ sourceVertexMap data wall right resolution hCompatible vertex ∈ side

@[simp] theorem mem_preimageSide (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (side : Finset data.SourceVertex) (vertex : (datum data wall right resolution hCompatible).SourceVertex) :
    vertex ∈ preimageSide data wall right resolution hCompatible side ↔
      sourceVertexMap data wall right resolution hCompatible vertex ∈ side := by
  simp [preimageSide]

/-- Vertex replacement restricted to a union of complete source fibres.
Only the selected wall blocks are replaced by their left and right blocks. -/
theorem card_preimageSide_add_wall (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (side : Finset data.SourceVertex) :
    (preimageSide data wall right resolution hCompatible side).card +
        (selectedWall data wall side).card =
      side.card +
        (selectedBlocks resolution.left (data.vertexPartition wall) (selectedWall data wall side)).card +
        (selectedBlocks resolution.right (data.vertexPartition wall) (selectedWall data wall side)).card := by
  have hOld := card_filter_sourceVertex target data (fun vertex ↦ vertex ∈ side)
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hOld
  have hUp : (preimageSide data wall right resolution hCompatible side).card =
      ∑ vertex : (graph target wall right).V,
        blockCount ((datum data wall right resolution hCompatible).vertexPartition vertex)
          (fun sheet ↦ sourceVertexMap data wall right resolution hCompatible
            ((datum data wall right resolution hCompatible).sourceEndpoint vertex sheet) ∈ side) := by
    convert card_filter_sourceVertex (graph target wall right)
      (datum data wall right resolution hCompatible)
      (fun vertex ↦ sourceVertexMap data wall right resolution hCompatible vertex ∈ side) using 1
    unfold preimageSide
    congr 1
    ext vertex
    simp
  have hUpProjected : (preimageSide data wall right resolution hCompatible side).card =
      ∑ vertex : TargetExpansion.Vertex target,
        blockCount ((datum data wall right resolution hCompatible).vertexPartition vertex)
          (fun sheet ↦ data.sourceEndpoint (contractVertex target wall vertex) sheet ∈ side) := by
    refine hUp.trans (Finset.sum_congr rfl fun vertex _ ↦ ?_)
    apply congrArg (blockCount _)
    funext sheet
    exact congrArg (fun point ↦ point ∈ side)
      (sourceVertexMap_sourceEndpoint data wall right resolution hCompatible hContracts vertex sheet)
  have hUp := hUpProjected.trans (TargetExpansion.sum_vertices target wall right
    (fun vertex ↦ blockCount ((datum data wall right resolution hCompatible).vertexPartition vertex)
      (fun sheet ↦ data.sourceEndpoint (contractVertex target wall vertex) sheet ∈ side)))
  have hAway (vertex : target.V) (hNe : vertex ≠ wall) :
      blockCount ((datum data wall right resolution hCompatible).vertexPartition (oldVertex target vertex))
          (fun sheet ↦ data.sourceEndpoint (contractVertex target wall (oldVertex target vertex)) sheet ∈ side) =
        blockCount (data.vertexPartition vertex) (fun sheet ↦ data.sourceEndpoint vertex sheet ∈ side) := by
    rw [datum_vertexPartition_old_of_ne data wall vertex right resolution hCompatible hNe]
    rfl
  have hUpOld :
      (∑ vertex : target.V,
        blockCount ((datum data wall right resolution hCompatible).vertexPartition (oldVertex target vertex))
          (fun sheet ↦ data.sourceEndpoint (contractVertex target wall (oldVertex target vertex)) sheet ∈ side)) =
      (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
        blockCount (data.vertexPartition vertex) (fun sheet ↦ data.sourceEndpoint vertex sheet ∈ side)) +
        blockCount resolution.left (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ wall)]
    congr 1
    · exact Finset.sum_congr rfl fun vertex hVertex ↦ hAway vertex (Finset.ne_of_mem_erase hVertex)
    · rw [datum_vertexPartition_old_wall]
      rfl
  rw [hUpOld, datum_vertexPartition_fresh] at hUp
  change (preimageSide data wall right resolution hCompatible side).card =
    (∑ vertex ∈ (Finset.univ : Finset target.V).erase wall,
      blockCount (data.vertexPartition vertex) (fun sheet ↦ data.sourceEndpoint vertex sheet ∈ side)) +
      blockCount resolution.left (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) +
      blockCount resolution.right (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) at hUp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ wall)] at hOld
  rw [blockCount_wall] at hOld
  rw [blockCount_eq_selectedBlocks, blockCount_eq_selectedBlocks] at hUp
  omega

/-- Internal edges are literal occurrences, so parallel edges are not lost. -/
noncomputable def insideEdges (data : GluingDatum target degree)
    (side : Finset data.SourceVertex) : Finset data.SourceEdge :=
  Finset.univ.filter fun edge ↦ (data.sourceEnds edge).1 ∈ side ∧ (data.sourceEnds edge).2 ∈ side

theorem card_insideEdges (data : GluingDatum target degree) (side : Finset data.SourceVertex) :
    (insideEdges data side).card = ∑ edge : target.edges,
      blockCount (data.edgePartition edge) (fun sheet ↦
        (data.sourceEnds (data.sourceEdge edge sheet)).1 ∈ side ∧
        (data.sourceEnds (data.sourceEdge edge sheet)).2 ∈ side) := by
  convert card_filter_sourceEdge target data
    (fun edge ↦ (data.sourceEnds edge).1 ∈ side ∧ (data.sourceEnds edge).2 ∈ side) using 1
  unfold insideEdges
  congr 1
  ext edge
  simp

theorem induced_edge_card (data : GluingDatum target degree)
    (side : Finset data.SourceVertex) (hSide : side.Nonempty) :
    (Utilities.inducedSubgraph data.sourceGraph side hSide).edges.card = (insideEdges data side).card := by
  trans (data.sourceGraph.edges.filter (fun edge ↦ edge.1 ∈ side ∧ edge.2 ∈ side)).card
  · exact Utilities.inducedSubgraph_edge_card_eq_filter data.sourceGraph side hSide
  unfold GluingDatum.sourceGraph insideEdges
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

theorem sourceEdge_old (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (edge : target.edges) (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).sourceEdge
        (occurrenceEquiv target wall right (some edge)) sheet =
      oldSourceEdge data wall right resolution hCompatible (data.sourceEdge edge sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg (fun partition : SheetPartition degree ↦ partition.repr sheet)
      (datum_edgePartition_old data wall right resolution hCompatible edge)

theorem sourceEdge_new (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution) (sheet : Fin degree) :
    (datum data wall right resolution hCompatible).sourceEdge
        (occurrenceEquiv target wall right none) sheet =
      newSourceEdge data wall right resolution hCompatible sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg (fun partition : SheetPartition degree ↦ partition.repr sheet)
      (datum_edgePartition_new data wall right resolution hCompatible)

theorem sourceMap_new_ends (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall)) (sheet : Fin degree) :
    (sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds
          (newSourceEdge data wall right resolution hCompatible sheet)).1,
      sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds
          (newSourceEdge data wall right resolution hCompatible sheet)).2) =
      (data.sourceEndpoint wall sheet, data.sourceEndpoint wall sheet) := by
  rw [sourceEnds_newSourceEdge]
  apply Prod.ext
  · exact sourceVertexMap_sourceEndpoint data wall right resolution hCompatible hContracts
      (oldVertex target wall) sheet
  · exact sourceVertexMap_sourceEndpoint data wall right resolution hCompatible hContracts
      (freshVertex target) sheet

/-- In a complete preimage side, retained inside occurrences are unchanged;
the only additional inside occurrences are the selected new-edge blocks. -/
theorem card_insideEdges_preimage (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (side : Finset data.SourceVertex) :
    (insideEdges (datum data wall right resolution hCompatible)
      (preimageSide data wall right resolution hCompatible side)).card =
      (insideEdges data side).card +
        (selectedBlocks resolution.newEdge (data.vertexPartition wall) (selectedWall data wall side)).card := by
  let mappedEnds (edge : (datum data wall right resolution hCompatible).SourceEdge) :=
    (sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds edge).1,
      sourceVertexMap data wall right resolution hCompatible
        ((datum data wall right resolution hCompatible).sourceEnds edge).2)
  let counts (edge : (graph target wall right).edges) :=
    blockCount ((datum data wall right resolution hCompatible).edgePartition edge)
      (fun sheet ↦
        (mappedEnds ((datum data wall right resolution hCompatible).sourceEdge edge sheet)).1 ∈ side ∧
        (mappedEnds ((datum data wall right resolution hCompatible).sourceEdge edge sheet)).2 ∈ side)
  have hCounts : (insideEdges (datum data wall right resolution hCompatible)
      (preimageSide data wall right resolution hCompatible side)).card = ∑ edge, counts edge := by
    refine (card_insideEdges _ _).trans (Finset.sum_congr rfl fun edge _ ↦ ?_)
    apply congrArg (blockCount _)
    funext sheet
    apply propext
    simp [preimageSide, mappedEnds]
  have hOld (edge : target.edges) : counts (occurrenceEquiv target wall right (some edge)) =
      blockCount (data.edgePartition edge) (fun sheet ↦
        (data.sourceEnds (data.sourceEdge edge sheet)).1 ∈ side ∧
        (data.sourceEnds (data.sourceEdge edge sheet)).2 ∈ side) := by
    dsimp only [counts]
    rw [datum_edgePartition_old]
    apply congrArg (blockCount _)
    funext sheet
    have hEnds := (congrArg mappedEnds (sourceEdge_old data wall right resolution hCompatible edge sheet)).trans
      (sourceVertexMap_sourceEnds_oldSourceEdge data wall right resolution hCompatible hContracts
        (data.sourceEdge edge sheet))
    exact congrArg (fun ends ↦ ends.1 ∈ side ∧ ends.2 ∈ side) hEnds
  have hNew : counts (occurrenceEquiv target wall right none) =
      blockCount resolution.newEdge (fun sheet ↦ data.sourceEndpoint wall sheet ∈ side) := by
    dsimp only [counts]
    rw [datum_edgePartition_new]
    apply congrArg (blockCount _)
    funext sheet
    have hEnds := (congrArg mappedEnds (sourceEdge_new data wall right resolution hCompatible sheet)).trans
      (sourceMap_new_ends data wall right resolution hCompatible hContracts sheet)
    exact (congrArg (fun ends ↦ ends.1 ∈ side ∧ ends.2 ∈ side) hEnds).trans
      (and_self _)
  have hCounts := hCounts.trans ((Equiv.sum_comp (occurrenceEquiv target wall right) counts).symm)
  rw [Fintype.sum_option, hNew] at hCounts
  simp_rw [hOld] at hCounts
  rw [← card_insideEdges data side, blockCount_eq_selectedBlocks] at hCounts
  omega

theorem genus_induced_eq (data : GluingDatum target degree)
    (side : Finset data.SourceVertex) (hSide : side.Nonempty) :
    genus (Utilities.inducedSubgraph data.sourceGraph side hSide) =
      ((insideEdges data side).card : ℤ) - (side.card : ℤ) + 1 :=
  congrArg₂ (fun edges vertices : ℕ ↦ (edges : ℤ) - (vertices : ℤ) + 1)
    (induced_edge_card data side hSide)
    (Utilities.inducedSubgraph_vertex_card data.sourceGraph side hSide)

theorem preimageSide_nonempty (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (side : Finset data.SourceVertex) (hSide : side.Nonempty) :
    (preimageSide data wall right resolution hCompatible side).Nonempty := by
  obtain ⟨vertex, hVertex⟩ := hSide
  obtain ⟨upstairs, hUpstairs⟩ := sourceVertexMap_surjective data wall right resolution hCompatible hContracts vertex
  refine ⟨upstairs, ?_⟩
  simpa [preimageSide, hUpstairs] using hVertex

/-- Contracting connected source fibres cannot increase the genus of an
induced side that is a union of complete fibres. This is a side-specific
Euler count, not an inference from equality of the whole-source genera.
No forest or danglingness-compatibility premise is needed. -/
theorem genus_side_le_preimage (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (side : Finset data.SourceVertex) (hSide : side.Nonempty) :
    genus (Utilities.inducedSubgraph data.sourceGraph side hSide) ≤
      genus (Utilities.inducedSubgraph (datum data wall right resolution hCompatible).sourceGraph
        (preimageSide data wall right resolution hCompatible side)
        (preimageSide_nonempty data wall right resolution hCompatible hContracts side hSide)) := by
  have hVertices := card_preimageSide_add_wall data wall right resolution hCompatible hContracts side
  have hEdges := card_insideEdges_preimage data wall right resolution hCompatible hContracts side
  have hLocal := selected_euler_le (data.vertexPartition wall) resolution hContracts (selectedWall data wall side)
  have hDown := genus_induced_eq data side hSide
  have hUp := genus_induced_eq (datum data wall right resolution hCompatible)
    (preimageSide data wall right resolution hCompatible side)
    (preimageSide_nonempty data wall right resolution hCompatible hContracts side hSide)
  omega

/-- For a genus-preserving resolution, every induced complete-preimage side
has exactly the old side's genus. The zero total Euler defect is distributed
over connected fibres, so no cancellation of positive local defects is possible. -/
theorem genus_side_eq_preimage (data : GluingDatum target degree) (wall : target.V)
    (right : target.edges → Bool) (resolution : LocalResolution degree)
    (hCompatible : OldCompatible data wall right resolution)
    (hContracts : resolution.ContractsTo (data.vertexPartition wall))
    (hGenus : genus (datum data wall right resolution hCompatible).sourceGraph = genus data.sourceGraph)
    (side : Finset data.SourceVertex) (hSide : side.Nonempty) :
    genus (Utilities.inducedSubgraph data.sourceGraph side hSide) =
      genus (Utilities.inducedSubgraph (datum data wall right resolution hCompatible).sourceGraph
        (preimageSide data wall right resolution hCompatible side)
        (preimageSide_nonempty data wall right resolution hCompatible hContracts side hSide)) := by
  have hVertices := card_preimageSide_add_wall data wall right resolution hCompatible hContracts side
  have hEdges := card_insideEdges_preimage data wall right resolution hCompatible hContracts side
  have hLocal := selected_euler_eq (data.vertexPartition wall) resolution hContracts
    ((sourceGraph_genus_eq_iff_block_card data wall right resolution hCompatible).mp hGenus)
    (selectedWall data wall side)
  have hDown := genus_induced_eq data side hSide
  have hUp := genus_induced_eq (datum data wall right resolution hCompatible)
    (preimageSide data wall right resolution hCompatible side)
    (preimageSide_nonempty data wall right resolution hCompatible hContracts side hSide)
  omega

end DraismaVargas.LocalCases.ResolutionSideCounts
