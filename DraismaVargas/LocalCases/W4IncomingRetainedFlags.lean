module

public import DraismaVargas.LocalCases.W4IncomingSideCensus
public import DraismaVargas.LocalCases.W4IncomingTargetNormalization
public import DraismaVargas.LocalCases.IncomingNormalizationRows

@[expose] public section

/-!
# Canonical incoming retained flags at a W4 wall

Source: Draisma–Vargas Part I, arXiv:1909.12924, Case {aux-r0} (`sub-r0`), the
auxiliary case of the four-valent (`w4`) wall. A retained wall occurrence
keeps its sheet representative and unfolds its target occurrence. Its
incoming endpoint over the merged wall is chosen by the actual right-side
predicate, not supplied as an incidence or contraction-map receipt.
-/

namespace DraismaVargas.LocalCases.W4IncomingRetainedFlags

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration FullContractionFibre PrunedFibreValency PrunedFibreTree
open IncomingW2TargetPlacement FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

section Dictionary

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The canonical same-sheet endpoint: the actual unfolded side determines
which of the original target endpoints carries it. -/
noncomputable def endpoint (edge : (contractDatum data hc hab hOne).SourceEdge) :
    data.SourceVertex :=
  data.sourceEndpoint (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a) edge.1.2

theorem endpoint_target (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (endpoint data hc hab hOne edge).1.1 =
      if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a := rfl

/-- The endpoint block is the original endpoint partition's block of the
unchanged wall sheet representative. -/
theorem endpoint_block (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (data.vertexPartition (endpoint data hc hab hOne edge).1.1).block
      (endpoint data hc hab hOne edge).1.2 =
    (data.vertexPartition (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a)).block
      edge.1.2 := by
  exact SheetPartition.block_eq_of_rel _ (SheetPartition.rel_repr_left _ _)

/-- A wall incidence yields an actual incoming incidence at the canonical
same-sheet endpoint. No incoming endpoint is supplied. -/
theorem endpoint_incident
    (block : (mergedPartition data a b).Blocks)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hIncident : Incident (contractDatum data hc hab hOne) edge (mergedVertex data hc hab hOne block)) :
    Incident data (sourceEdgeEmbedding data hc hab hOne edge) (endpoint data hc hab hOne edge) := by
  have hWall := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne) edge
    (mergedVertex data hc hab hOne block)).mp hIncident).1
  have hVal := IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne edge
  apply (incident_iff_target_mem_and_rel data _ _).mpr
  have hTarget := congrArg Prod.fst hVal
  have hSheet := congrArg Prod.snd hVal
  rw [hTarget, hSheet]
  change unfoldEdge hc hab hOne edge.1.1 ∈ GluingDatum.incidentEdges
    (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a) ∧
    (data.vertexPartition (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a)).Rel
      ((data.vertexPartition (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a)).repr edge.1.2)
      edge.1.2
  refine ⟨?_, SheetPartition.rel_repr_left _ _⟩
  cases hSide : IncomingTargetExpansion.right hc hab hOne edge.1.1 with
  | false => exact (right_eq_false_iff_of_incident hc hab hOne _ hWall).mp hSide
  | true => exact (right_eq_true_iff hc hab hOne _).mp hSide

/-- The canonical endpoint contracts to the specified wall block. -/
theorem endpoint_map
    (block : (mergedPartition data a b).Blocks)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hIncident : Incident (contractDatum data hc hab hOne) edge (mergedVertex data hc hab hOne block)) :
    sourceVertexMap data hc hab hOne (endpoint data hc hab hOne edge) =
      mergedVertex data hc hab hOne block := by
  have hRel := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne) edge
    (mergedVertex data hc hab hOne block)).mp hIncident).2
  let side := if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a
  have hFold : fold target hab side = ⟨a, hab⟩ := by
    dsimp only [side]
    split <;> simp only [fold_self, fold_a]
  change (contractDatum data hc hab hOne).sourceEndpoint (fold target hab side)
    ((data.vertexPartition side).repr edge.1.2) = _
  rw [← sourceEndpoint_repr, hFold]
  exact ((contractDatum data hc hab hOne).sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, hRel.symm⟩

/-- The canonical incoming copy is a genuine retained boundary occurrence
of this exact merged source block. -/
theorem embedding_mem_boundary
    (hPreserved : DanglingPreserved data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (edge : NonDanglingEdge (contractDatum data hc hab hOne))
    (hIncident : Incident (contractDatum data hc hab hOne) edge.1 (mergedVertex data hc hab hOne block)) :
    (nonDanglingEmbedding data hPreserved edge).1 ∈
      boundaryEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
  apply (mem_boundaryEdges data hc hab hOne _ _).mpr
  refine ⟨(nonDanglingEmbedding data hPreserved edge).2,
    sourceEdgeEmbedding_ne_contracted data hc hab hOne edge.1, ?_⟩
  have hInc := endpoint_incident data hc hab hOne block edge.1 hIncident
  have hMap := endpoint_map data hc hab hOne block edge.1 hIncident
  exact hInc.imp (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)
    (fun h ↦ (congrArg (sourceVertexMap data hc hab hOne) h).trans hMap)

/-- No other endpoint in the same contraction fibre meets this retained
occurrence. This is occurrencewise looplessness, not an assumed no-return. -/
theorem endpoint_unique
    (hPreserved : DanglingPreserved data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (edge : NonDanglingEdge (contractDatum data hc hab hOne))
    (hIncident : Incident (contractDatum data hc hab hOne) edge.1 (mergedVertex data hc hab hOne block))
    (point : data.SourceVertex)
    (hMap : sourceVertexMap data hc hab hOne point = mergedVertex data hc hab hOne block)
    (hInc : Incident data (nonDanglingEmbedding data hPreserved edge).1 point) :
    point = endpoint data hc hab hOne edge.1 :=
  W4IncomingSideCensus.boundary_endpoint_unique data hc hab hOne _ _
    (embedding_mem_boundary data hc hab hOne hPreserved block edge hIncident) point _ hMap
    (endpoint_map data hc hab hOne block edge.1 hIncident) hInc
    (endpoint_incident data hc hab hOne block edge.1 hIncident)

/-- The canonical endpoint belongs to the actual active fibre. -/
theorem endpoint_active
    (hPreserved : DanglingPreserved data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (edge : NonDanglingEdge (contractDatum data hc hab hOne))
    (hIncident : Incident (contractDatum data hc hab hOne) edge.1 (mergedVertex data hc hab hOne block)) :
    endpoint data hc hab hOne edge.1 ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) :=
  W4IncomingSideCensus.active_of_boundary_incident data hc hab hOne _ _
    (embedding_mem_boundary data hc hab hOne hPreserved block edge hIncident) _
    (endpoint_map data hc hab hOne block edge.1 hIncident)
    (endpoint_incident data hc hab hOne block edge.1 hIncident)

/-- Distinct literal wall flags remain distinct incoming source occurrences;
no statement about distinct stable rows is made. -/
theorem embedding_ne
    (hPreserved : DanglingPreserved data hc hab hOne)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne)) (hNe : first ≠ second) :
    (nonDanglingEmbedding data hPreserved first).1 ≠
      (nonDanglingEmbedding data hPreserved second).1 := by
  intro h
  exact hNe (nonDanglingEmbedding_injective data hPreserved (Subtype.ext h))

/-- The actual incoming retained occurrence has exactly the wall occurrence's
sheet block, not merely its dilation index. -/
theorem embedding_block (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (data.edgePartition (sourceEdgeEmbedding data hc hab hOne edge).1.1).block
      (sourceEdgeEmbedding data hc hab hOne edge).1.2 =
      ((contractDatum data hc hab hOne).edgePartition edge.1.1).block edge.1.2 := by
  have hVal := IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne edge
  rw [congrArg Prod.fst hVal, congrArg Prod.snd hVal]
  rfl

/-- The unchanged retained sheet block refines the canonical incoming endpoint block. -/
theorem block_subset_endpoint_block
    (block : (mergedPartition data a b).Blocks)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hIncident : Incident (contractDatum data hc hab hOne) edge (mergedVertex data hc hab hOne block)) :
    ((contractDatum data hc hab hOne).edgePartition edge.1.1).block edge.1.2 ⊆
      (data.vertexPartition (endpoint data hc hab hOne edge).1.1).block
        (endpoint data hc hab hOne edge).1.2 := by
  rw [← embedding_block data hc hab hOne edge]
  obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data _ _).mp
    (endpoint_incident data hc hab hOne block edge hIncident)
  intro sheet hSheet
  exact (SheetPartition.mem_block_iff _ _ _).mpr
    (hRel.trans ((StableLocalProperties.refines_of_mem_incidentEdges data hAt).rel
      ((SheetPartition.mem_block_iff _ _ _).mp hSheet)))

/-- Equality of the canonical endpoint target sides is exactly equality of
the actual reconstructed Boolean placements. -/
theorem endpoint_target_eq_iff
    (first second : (contractDatum data hc hab hOne).SourceEdge) :
    (endpoint data hc hab hOne first).1.1 = (endpoint data hc hab hOne second).1.1 ↔
      IncomingTargetExpansion.right hc hab hOne first.1.1 =
        IncomingTargetExpansion.right hc hab hOne second.1.1 := by
  cases hFirst : IncomingTargetExpansion.right hc hab hOne first.1.1 <;>
    cases hSecond : IncomingTargetExpansion.right hc hab hOne second.1.1 <;>
    simp [endpoint_target, hFirst, hSecond, hab, Ne.symm hab]

end Dictionary

section Pairing

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

/-- The possible global endpoint swap cancels in comparisons of two target
sides, giving the actual canonical W4 pairing comparison. -/
theorem endpoint_side_eq_iff_pairing
    (block : (mergedPartition data a b).Blocks)
    (first second : (contractDatum data hc hab hOne).SourceEdge)
    (hFirst : Incident (contractDatum data hc hab hOne) first (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second (mergedVertex data hc hab hOne block)) :
    (endpoint data hc hab hOne first).1.1 = (endpoint data hc hab hOne second).1.1 ↔
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1 =
        star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1 := by
  have hFirstAt := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne) first
    (mergedVertex data hc hab hOne block)).mp hFirst).1
  have hSecondAt := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne) second
    (mergedVertex data hc hab hOne block)).mp hSecond).1
  rw [endpoint_target_eq_iff]
  rcases W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star with h | h
  · rw [h _ hFirstAt, h _ hSecondAt]
  · rw [h _ hFirstAt, h _ hSecondAt]
    exact ⟨Bool.not_inj, congrArg Bool.not⟩

theorem endpoint_side_ne_iff_pairing
    (block : (mergedPartition data a b).Blocks)
    (first second : (contractDatum data hc hab hOne).SourceEdge)
    (hFirst : Incident (contractDatum data hc hab hOne) first (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second (mergedVertex data hc hab hOne block)) :
    (endpoint data hc hab hOne first).1.1 ≠ (endpoint data hc hab hOne second).1.1 ↔
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1 ≠
        star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1 :=
  not_congr (endpoint_side_eq_iff_pairing data fd hc hab hOne star block first second hFirst hSecond)

/-- Canonical nd2 same-side census: callers supply only actual wall flags
and their wall incidences, never incoming endpoint or boundary receipts. -/
theorem nd2_same_pairing_side
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block) = 2)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne)) (hNe : first ≠ second)
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hSide : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 =
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1) :
    endpoint data hc hab hOne first.1 = endpoint data hc hab hOne second.1 ∧
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
        {endpoint data hc hab hOne first.1} ∧
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = ∅ ∧
      nonDanglingValency data (endpoint data hc hab hOne first.1) = 2 :=
  W4IncomingSideCensus.nd2_same_side data fd hc hab hOne star hCompat _ hNd
    _ _ (embedding_ne data hc hab hOne hCompat.1 first second hNe)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block first hFirst)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block second hSecond)
    _ _ (endpoint_map data hc hab hOne block first.1 hFirst)
    (endpoint_map data hc hab hOne block second.1 hSecond)
    (endpoint_incident data hc hab hOne block first.1 hFirst)
    (endpoint_incident data hc hab hOne block second.1 hSecond)
    ((endpoint_side_eq_iff_pairing data fd hc hab hOne star block first.1 second.1 hFirst hSecond).mpr hSide)

/-- Canonical nd2 opposite-side census on the same actual wall flags. -/
theorem nd2_opposite_pairing_sides
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block) = 2)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne))
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hSide : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 ≠
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
        {endpoint data hc hab hOne first.1, endpoint data hc hab hOne second.1} ∧
      Incident data edge (endpoint data hc hab hOne first.1) ∧
      Incident data edge (endpoint data hc hab hOne second.1) ∧
      nonDanglingValency data (endpoint data hc hab hOne first.1) = 2 ∧
      nonDanglingValency data (endpoint data hc hab hOne second.1) = 2 :=
  W4IncomingSideCensus.nd2_opposite_sides data fd hc hab hOne star hCompat _ hNd _ _
    (embedding_mem_boundary data hc hab hOne hCompat.1 block first hFirst)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block second hSecond)
    _ _ (endpoint_map data hc hab hOne block first.1 hFirst)
    (endpoint_map data hc hab hOne block second.1 hSecond)
    (endpoint_incident data hc hab hOne block first.1 hFirst)
    (endpoint_incident data hc hab hOne block second.1 hSecond)
    ((endpoint_side_ne_iff_pairing data fd hc hab hOne star block first.1 second.1 hFirst hSecond).mpr hSide)

/-- Canonical nd3 singleton/pair-side census, with no supplied incoming
endpoint, boundary-membership, or incidence-map receipts. -/
theorem nd3_singleton_pairing_side
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block) = 3)
    (first second third : NonDanglingEdge (contractDatum data hc hab hOne)) (hNe : second ≠ third)
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hThird : Incident (contractDatum data hc hab hOne) third.1 (mergedVertex data hc hab hOne block))
    (hOpposite : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 ≠
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1)
    (hSame : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1 =
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) third.1.1.1) :
    endpoint data hc hab hOne second.1 = endpoint data hc hab hOne third.1 ∧
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
        {endpoint data hc hab hOne first.1, endpoint data hc hab hOne second.1} ∧
      Incident data edge (endpoint data hc hab hOne first.1) ∧
      Incident data edge (endpoint data hc hab hOne second.1) ∧
      nonDanglingValency data (endpoint data hc hab hOne first.1) = 2 ∧
      nonDanglingValency data (endpoint data hc hab hOne second.1) = 3 :=
  W4IncomingSideCensus.nd3_singleton_side data fd hc hab hOne star hCompat _ hNd _ _ _
    (embedding_ne data hc hab hOne hCompat.1 second third hNe)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block first hFirst)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block second hSecond)
    (embedding_mem_boundary data hc hab hOne hCompat.1 block third hThird)
    _ _ _ (endpoint_map data hc hab hOne block first.1 hFirst)
    (endpoint_map data hc hab hOne block second.1 hSecond)
    (endpoint_map data hc hab hOne block third.1 hThird)
    (endpoint_incident data hc hab hOne block first.1 hFirst)
    (endpoint_incident data hc hab hOne block second.1 hSecond)
    (endpoint_incident data hc hab hOne block third.1 hThird)
    ((endpoint_side_ne_iff_pairing data fd hc hab hOne star block first.1 second.1 hFirst hSecond).mpr hOpposite)
    ((endpoint_side_eq_iff_pairing data fd hc hab hOne star block second.1 third.1 hSecond hThird).mpr hSame)

end Pairing

end DraismaVargas.LocalCases.W4IncomingRetainedFlags
