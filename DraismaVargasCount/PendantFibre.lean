module

public import DraismaVargasCount.IndexPattern
public import DraismaVargas.LocalCases.DanglingSideStructure

@[expose] public section

/-!
# The actual pullback fibre on a pendant side

A geometric input to the chip coefficients of a member's pencil: which chips of a pulled
back fibre can lie on a pendant (dangling) side of the source.
The no-glue and dangling-Riemann--Hurwitz theorems make every
vertex of an actual dangling side a singleton sheet block. Connectedness then
propagates that literal sheet across the side, proving that target projection
is injective. Consequently every target fibre has weight zero or one on the
side, and the fibre over its attachment has weight zero there.

No retracted divisor or target-branch bijection is assumed. Identifying which
target branch supplies the one chip, and assembling all attached sides into
the actual retracted divisor, remain separate geometric tasks. This file does not give
the complete chip-coefficient classification.
-/

namespace DraismaVargas.Count.PendantFibre

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases
open W4StableSource StableLocalProperties FullDimensionalSource
open DanglingSideStructure DanglingDescent

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Every source vertex entirely removed by pruning is unramified and has
local degree one. These are the dangling-RH and no-glue theorems
read at the vertex, before extracting their global consequence. -/
theorem degree_one_of_nonDanglingValency_zero
    (fd : FullDimensionalSourcePresentation data coordinate)
    (vertex : data.SourceVertex) (hZero : nonDanglingValency data vertex = 0) :
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1 ∧
      data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 := by
  have hDangling := (nonDanglingValency_eq_zero_iff data vertex).mp hZero
  have hRam := localRamification_eq_zero_of_forall_isDangling data fd.valid
    fd.changeMinimal fd.labelling fd.det_ne_zero vertex (fun edge ↦ hDangling edge.1 edge.2)
  exact ⟨blockCard_eq_one_of_forall_sourceEdgeIndex_eq_one data vertex
    (fun edge ↦ fd.danglingEdgeNoGlue edge.1 (hDangling edge.1 edge.2)) hRam, hRam⟩

/-- At a singleton source block the sheet stored in any incident occurrence
is exactly the sheet stored in the vertex. -/
theorem edge_sheet_eq_of_blockCard_one {vertex : data.SourceVertex}
    (hOne : (data.vertexPartition vertex.1.1).blockCard vertex.1.2 = 1)
    {edge : data.SourceEdge} (hIncident : Incident data edge vertex) :
    edge.1.2 = vertex.1.2 := by
  have hMem := (data.vertexPartition vertex.1.1).mem_block_iff vertex.1.2 edge.1.2 |>.mpr
    ((incident_iff_target_mem_and_rel data edge vertex).mp hIncident).2
  rw [(data.vertexPartition vertex.1.1).block_eq_singleton_of_blockCard_eq_one
    vertex.1.2 hOne, Finset.mem_singleton] at hMem
  exact hMem

/-- Adjacent singleton vertices have the same literal sheet. -/
theorem sheet_eq_of_adjacent_of_blockCard_one {first second : data.SourceVertex}
    (hFirst : (data.vertexPartition first.1.1).blockCard first.1.2 = 1)
    (hSecond : (data.vertexPartition second.1.1).blockCard second.1.2 = 1)
    (hAdj : 0 < num_edges data.sourceGraph first second) : first.1.2 = second.1.2 := by
  obtain ⟨edge, hEnds | hEnds⟩ := exists_sourceEnds_of_num_edges_pos data hAdj
  · exact (edge_sheet_eq_of_blockCard_one hFirst (Or.inl (congrArg Prod.fst hEnds))).symm.trans
      (edge_sheet_eq_of_blockCard_one hSecond (Or.inr (congrArg Prod.snd hEnds)))
  · exact (edge_sheet_eq_of_blockCard_one hFirst (Or.inr (congrArg Prod.snd hEnds))).symm.trans
      (edge_sheet_eq_of_blockCard_one hSecond (Or.inl (congrArg Prod.fst hEnds)))

/-- The entire actual pendant side is one sheet: this uses connectedness of
the side and the singleton blocks produced by the full-dimensional datum. -/
theorem sheet_eq_of_mem_side (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    {vertex : data.SourceVertex} (hVertex : vertex ∈ cut.side) :
    vertex.1.2 = inner.1.2 := by
  let sideGraph := Utilities.inducedSubgraph data.sourceGraph cut.side ⟨inner, cut.left_mem⟩
  have hReach : Reach sideGraph ⟨inner, cut.left_mem⟩ ⟨vertex, hVertex⟩ :=
    reach_of_graph_connected cut.side_connected _ _
  refine reach_propagate (motive := fun item : sideGraph.V ↦ item.1.1.2 = inner.1.2)
    rfl (fun first second hAdj hFirst ↦ ?_) hReach
  have hAdj' : 0 < num_edges data.sourceGraph first.1 second.1 := by
    have hCount := Utilities.num_edges_inducedSubgraph data.sourceGraph cut.side
      ⟨inner, cut.left_mem⟩ first second
    exact lt_of_lt_of_eq hAdj hCount
  have hEqual := sheet_eq_of_adjacent_of_blockCard_one
    (degree_one_of_nonDanglingValency_zero fd first.1
      (nonDanglingValency_eq_zero_of_mem_side data cut first.2)).1
    (degree_one_of_nonDanglingValency_zero fd second.1
      (nonDanglingValency_eq_zero_of_mem_side data cut second.2)).1 hAdj'
  exact hEqual.symm.trans hFirst

/-- Target projection is injective on an actual pendant side. This is the
global fibre census, derived from the literal sheet labels rather than assumed
as a local-isomorphism hypothesis. -/
theorem target_injective_on_side (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer) :
    Set.InjOn (fun vertex : data.SourceVertex ↦ vertex.1.1)
      {vertex | vertex ∈ cut.side} := by
  intro first hFirst second hSecond hTarget
  apply Subtype.ext
  exact Prod.ext hTarget ((sheet_eq_of_mem_side fd cut hFirst).trans
    (sheet_eq_of_mem_side fd cut hSecond).symm)

/-- A pendant side cannot contain a second point over its attachment vertex.
The cut occurrence identifies its unique sheet with the attachment block. -/
theorem target_ne_outer_of_mem_side
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    {vertex : data.SourceVertex} (hVertex : vertex ∈ cut.side) :
    vertex.1.1 ≠ outer.1.1 := by
  have hAdj : 0 < num_edges data.sourceGraph inner outer := by
    have hEq : num_edges data.sourceGraph inner outer = 1 :=
      (cut.cross_num_edges inner outer cut.left_mem cut.right_not_mem).trans
        (ite_eq_left ⟨rfl, rfl⟩)
    exact lt_of_lt_of_eq (by decide : 0 < 1) hEq.symm
  obtain ⟨edge, hEnds⟩ := exists_sourceEnds_of_num_edges_pos data hAdj
  have hInner : Incident data edge inner := by
    rcases hEnds with h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.snd h)
  have hOuter : Incident data edge outer := by
    rcases hEnds with h | h
    · exact Or.inr (congrArg Prod.snd h)
    · exact Or.inl (congrArg Prod.fst h)
  have hSheet := edge_sheet_eq_of_blockCard_one
    (degree_one_of_nonDanglingValency_zero fd inner
      (nonDanglingValency_eq_zero_of_mem_side data cut cut.left_mem)).1 hInner
  have hRel := ((incident_iff_target_mem_and_rel data edge outer).mp hOuter).2
  rw [hSheet] at hRel
  have hAttach : data.sourceEndpoint outer.1.1 inner.1.2 = outer :=
    (data.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, hRel.symm⟩
  intro hTarget
  have hEndpoint := data.sourceEndpoint_self vertex
  rw [hTarget, sheet_eq_of_mem_side fd cut hVertex, hAttach] at hEndpoint
  exact cut.right_not_mem (hEndpoint ▸ hVertex)

/-- The actual pullback fibre on a pendant side contains at most one vertex,
and its multiplicity is one. No retraction map is postulated here. -/
theorem fibre_sum_eq_indicator
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    (root : target.V) :
    (∑ vertex ∈ cut.side,
      if vertex.1.1 = root then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0) =
      if ∃ vertex ∈ cut.side, vertex.1.1 = root then 1 else 0 := by
  classical
  by_cases hExists : ∃ vertex ∈ cut.side, vertex.1.1 = root
  · rw [ite_eq_left hExists]
    obtain ⟨chosen, hChosen, hTarget⟩ := hExists
    rw [Finset.sum_eq_single chosen]
    · rw [ite_eq_left hTarget, (degree_one_of_nonDanglingValency_zero fd chosen
        (nonDanglingValency_eq_zero_of_mem_side data cut hChosen)).1]
      rfl
    · intro vertex hVertex hNe
      rw [ite_eq_right]
      intro hEq
      exact hNe (target_injective_on_side fd cut hVertex hChosen (hEq.trans hTarget.symm))
    · exact fun h ↦ (h hChosen).elim
  · rw [ite_eq_right hExists]
    apply Finset.sum_eq_zero
    intro vertex hVertex
    exact ite_eq_right (fun h ↦ hExists ⟨vertex, hVertex, h⟩)

/-- No chips of the fibre over the attachment itself lie in its pendant side. -/
theorem fibre_sum_at_attachment_eq_zero
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer) :
    (∑ vertex ∈ cut.side,
      if vertex.1.1 = outer.1.1 then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0) = 0 := by
  rw [fibre_sum_eq_indicator fd cut]
  exact ite_eq_right (by
    rintro ⟨vertex, hVertex, hEqual⟩
    exact target_ne_outer_of_mem_side fd cut hVertex hEqual)

end DraismaVargas.Count.PendantFibre

