import DraismaVargasCount.PendantFibre

/-!
# The target branch is exactly the image of an actual pendant side

This continues the geometric input to the chip-coefficient classification
(`RowChipCoefficient`) begun in `PendantFibre`.
Every target adjacency lifts through a specified sheet. A target walk avoiding
the attachment therefore lifts inside the actual dangling cut, because its
only crossing ends at the attachment. Conversely side connectivity and the
proved absence of points over the attachment project to such target walks.

The resulting `fibre_sum_eq_branch_indicator` counts actual pullback weights:
one chip precisely when the root lies in that target branch, zero otherwise.
Neither a branch bijection nor a retracted coefficient law is assumed.
Aggregating the incident pendant components into the retracted divisor is done in
`PendantRetraction`, and its interior-row coefficients are classified in
`RowChipCoefficient`.
-/

namespace DraismaVargas.Count.PendantFibre

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases
open W4StableSource StableLocalProperties FullDimensionalSource
open DanglingSideStructure DanglingDescent

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Adjacency in the target lifts through the sheet of any source vertex. -/
theorem target_adjacent_lift (vertex : data.SourceVertex) (next : target.V)
    (hAdj : 0 < num_edges target vertex.1.1 next) :
    0 < num_edges data.sourceGraph vertex (data.sourceEndpoint next vertex.1.2) := by
  classical
  obtain ⟨pair, hPair, hEnds⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos target vertex.1.1 next hAdj
  let targetEdge : target.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  have hFirstMem : targetEdge ∈ incidentEdges vertex.1.1 := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    change pair.1 = vertex.1.1 ∨ pair.2 = vertex.1.1
    rcases hEnds with h | h <;> simp [h]
  have hSecondMem : targetEdge ∈ incidentEdges next := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    change pair.1 = next ∨ pair.2 = next
    rcases hEnds with h | h <;> simp [h]
  have hFirst := incident_sourceEdge_sourceEndpoint data vertex.1.1 targetEdge
    hFirstMem vertex.1.2
  rw [data.sourceEndpoint_self vertex] at hFirst
  have hSecond := incident_sourceEdge_sourceEndpoint data next targetEdge
    hSecondMem vertex.1.2
  have hNeTarget : vertex.1.1 ≠ next := by
    intro hEq
    have hDiagonal : pair = (vertex.1.1, vertex.1.1) := by
      rcases hEnds with h | h
      · exact h.trans (Prod.ext rfl hEq.symm)
      · exact h.trans (Prod.ext hEq.symm rfl)
    exact target.loopless vertex.1.1 (hDiagonal ▸ hPair)
  have hNe : vertex ≠ data.sourceEndpoint next vertex.1.2 := by
    intro hEq
    exact hNeTarget (congrArg (fun v : data.SourceVertex ↦ v.1.1) hEq)
  apply num_edges_pos_of_sourceEnds data (edge := data.sourceEdge targetEdge vertex.1.2)
  rcases hFirst with hFirst | hFirst <;> rcases hSecond with hSecond | hSecond
  · exact (hNe (hFirst.symm.trans hSecond)).elim
  · exact Or.inl (Prod.ext hFirst hSecond)
  · exact Or.inr (Prod.ext hSecond hFirst)
  · exact (hNe (hFirst.symm.trans hSecond)).elim

/-- Every target walk avoiding the attachment lifts inside the actual
pendant side. The cut's unique crossing is the only excluded step. -/
theorem exists_in_side_of_target_reach
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    {root : target.V}
    (hReach : ReachP target (fun v ↦ v ≠ outer.1.1) inner.1.1 root) :
    ∃ vertex ∈ cut.side, vertex.1.1 = root := by
  induction hReach with
  | refl => exact ⟨inner, cut.left_mem, rfl⟩
  | @tail before next _ hStep ih =>
    obtain ⟨vertex, hVertex, hTarget⟩ := ih
    let lifted := data.sourceEndpoint next vertex.1.2
    have hAdj : 0 < num_edges data.sourceGraph vertex lifted :=
      target_adjacent_lift vertex next (hTarget ▸ hStep.1)
    refine ⟨lifted, ?_, rfl⟩
    by_contra hOutside
    have hCut := cut.cross_num_edges vertex lifted hVertex hOutside
    have hPair : vertex = inner ∧ lifted = outer := by
      by_contra hNot
      exact (Nat.ne_of_gt hAdj) (hCut.trans (if_neg hNot))
    exact hStep.2 (congrArg (fun v : data.SourceVertex ↦ v.1.1) hPair.2)

/-- The quotient-source target projection preserves adjacency. -/
theorem target_adjacent_of_source_adjacent {first second : data.SourceVertex}
    (hAdj : 0 < num_edges data.sourceGraph first second) :
    0 < num_edges target first.1.1 second.1.1 := by
  obtain ⟨edge, hEnds⟩ := exists_sourceEnds_of_num_edges_pos data hAdj
  apply TargetSeparation.num_edges_pos_of_ends (edge := edge.1.1)
  rcases hEnds with hEnds | hEnds
  · exact Or.inl (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
      (ends.1.1.1, ends.2.1.1)) hEnds)
  · exact Or.inr (congrArg (fun ends : data.SourceVertex × data.SourceVertex ↦
      (ends.1.1.1, ends.2.1.1)) hEnds)

/-- Every point of a pendant side projects into its target branch. -/
theorem target_reach_of_mem_side
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    {vertex : data.SourceVertex} (hVertex : vertex ∈ cut.side) :
    ReachP target (fun v ↦ v ≠ outer.1.1) inner.1.1 vertex.1.1 := by
  let sideGraph := Utilities.inducedSubgraph data.sourceGraph cut.side ⟨inner, cut.left_mem⟩
  have hReach : Reach sideGraph ⟨inner, cut.left_mem⟩ ⟨vertex, hVertex⟩ :=
    reach_of_graph_connected cut.side_connected _ _
  refine reach_propagate
    (motive := fun item : sideGraph.V ↦
      ReachP target (fun v ↦ v ≠ outer.1.1) inner.1.1 item.1.1.1)
    (reachP_refl _ _) (fun before next hAdj ih ↦ ?_) hReach
  exact reachP_tail ih
    (target_adjacent_of_source_adjacent (lt_of_lt_of_eq hAdj
      (Utilities.num_edges_inducedSubgraph data.sourceGraph cut.side
        ⟨inner, cut.left_mem⟩ before next)))
    (target_ne_outer_of_mem_side fd cut next.2)

/-- The image of the actual pendant side is exactly the target branch cut
off from the attachment, expressed by walks avoiding that target vertex. -/
theorem exists_in_side_target_iff
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    (root : target.V) :
    (∃ vertex ∈ cut.side, vertex.1.1 = root) ↔
      ReachP target (fun v ↦ v ≠ outer.1.1) inner.1.1 root := by
  constructor
  · rintro ⟨vertex, hVertex, rfl⟩
    exact target_reach_of_mem_side fd cut hVertex
  · exact exists_in_side_of_target_reach cut

/-- The exact geometric census needed for the chip-coefficient classification: a dangling component
contributes one chip precisely when the target root lies beyond its cut edge. -/
theorem fibre_sum_eq_branch_indicator
    (fd : FullDimensionalSourcePresentation data coordinate)
    {inner outer : data.SourceVertex} (cut : DanglingSide data.sourceGraph inner outer)
    (root : target.V) :
    (∑ vertex ∈ cut.side,
      if vertex.1.1 = root then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0) =
      if ReachP target (fun v ↦ v ≠ outer.1.1) inner.1.1 root then 1 else 0 := by
  classical
  rw [fibre_sum_eq_indicator fd cut]
  exact if_congr (exists_in_side_target_iff fd cut root) rfl rfl

end DraismaVargas.Count.PendantFibre
