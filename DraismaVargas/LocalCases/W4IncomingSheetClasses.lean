import DraismaVargas.LocalCases.W4IncomingRetainedFlags
import DraismaVargas.LocalCases.W4IncomingClassUnion

/-!
# Literal sheet classes in the incoming auxiliary r0 cases

Source: Draisma–Vargas Part I, arXiv:1909.12924, Case {aux-r0} (`sub-r0`),
sub-cases {aux-r0-nd2} and {aux-r0-nd3}. The canonical retained flags determine
the active endpoints and their valencies. Local r0 identifies every class at a
divalent endpoint; non-dangling union (`lemma-class-union`) then identifies the
whole merged class.
The conclusions identify actual sheet sets, not just their cardinalities.
-/

namespace DraismaVargas.LocalCases.W4IncomingSheetClasses

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification W4StableSource StableLocalProperties WallDegeneration
open FullContractionFibre PrunedFibreValency PrunedFibreTree FullDimensionalSource
open W4IncomingRetainedFlags W4IncomingClassUnion

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

omit [Fintype coordinate] [DecidableEq coordinate] fd star in
/-- Canonical incoming flag endpoints really lie over the two contracted ends. -/
theorem endpoint_above (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (endpoint data hc hab hOne edge).1.1 = a ∨
      (endpoint data hc hab hOne edge).1.1 = b := by
  rw [endpoint_target]
  split <;> simp

/-- At a divalent canonical endpoint, its class is exactly the unchanged
retained wall class. -/
theorem endpoint_block_eq_flag
    (hPreserved : DanglingPreserved data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (edge : NonDanglingEdge (contractDatum data hc hab hOne))
    (hIncident : Incident (contractDatum data hc hab hOne) edge.1
      (mergedVertex data hc hab hOne block))
    (hNd : nonDanglingValency data (endpoint data hc hab hOne edge.1) = 2) :
    (data.vertexPartition (endpoint data hc hab hOne edge.1).1.1).block
        (endpoint data hc hab hOne edge.1).1.2 =
      ((contractDatum data hc hab hOne).edgePartition edge.1.1.1).block edge.1.1.2 := by
  have h := W4IncomingCensus.block_eq_of_survives_nd2_at_endpoint data fd hc hab hOne star
    _ (endpoint_above data hc hab hOne edge.1) hNd
    (nonDanglingEmbedding data hPreserved edge).1
    (nonDanglingEmbedding data hPreserved edge).2
    (endpoint_incident data hc hab hOne block edge.1 hIncident)
  exact h.symm.trans (embedding_block data hc hab hOne edge.1)

/-- With both flags on one side, the unique active vertex is the entire
merged class; both retained surviving classes equal it. -/
theorem nd2_same_side_classes
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 2)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne)) (hNe : first ≠ second)
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hSide : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 =
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1) :
    (data.vertexPartition (endpoint data hc hab hOne first.1).1.1).block
        (endpoint data hc hab hOne first.1).1.2 = (mergedPartition data a b).block block.1 ∧
      ((contractDatum data hc hab hOne).edgePartition first.1.1.1).block first.1.1.2 =
        (mergedPartition data a b).block block.1 ∧
      ((contractDatum data hc hab hOne).edgePartition second.1.1.1).block second.1.1.2 =
        (mergedPartition data a b).block block.1 := by
  obtain ⟨hEqual, hActive, _, hFirstNd⟩ :=
    nd2_same_pairing_side data fd hc hab hOne star hCompat block hNd first second hNe hFirst hSecond hSide
  have hMerged := block_eq_of_active_singleton data fd hc hab hOne star block _ hActive
  have hFirstBlock := endpoint_block_eq_flag data fd hc hab hOne star hCompat.1 block first hFirst hFirstNd
  have hSecondNd : nonDanglingValency data (endpoint data hc hab hOne second.1) = 2 := by
    rw [← hEqual]; exact hFirstNd
  have hSecondBlock := endpoint_block_eq_flag data fd hc hab hOne star hCompat.1 block second hSecond hSecondNd
  rw [← hEqual] at hSecondBlock
  exact ⟨hMerged.symm, hFirstBlock.symm.trans hMerged.symm, hSecondBlock.symm.trans hMerged.symm⟩

/-- With opposite flags, both endpoints and the unique internal occurrence
have exactly the whole merged sheet class. -/
theorem nd2_opposite_side_classes
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 2)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne))
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hSide : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 ≠
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      (data.edgePartition edge.1.1).block edge.1.2 = (mergedPartition data a b).block block.1 ∧
      (data.vertexPartition (endpoint data hc hab hOne first.1).1.1).block
        (endpoint data hc hab hOne first.1).1.2 = (mergedPartition data a b).block block.1 ∧
      (data.vertexPartition (endpoint data hc hab hOne second.1).1.1).block
        (endpoint data hc hab hOne second.1).1.2 = (mergedPartition data a b).block block.1 := by
  classical
  obtain ⟨edge, hEdge, hActive, hEdgeFirst, hEdgeSecond, hFirstNd, hSecondNd⟩ :=
    nd2_opposite_pairing_sides data fd hc hab hOne star hCompat block hNd first second hFirst hSecond hSide
  have hMember : edge ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
    rw [hEdge]; simp
  have hSurvives := ((mem_internalEdges data hc hab hOne _ edge).mp hMember).1
  have hFirstBlock := W4IncomingCensus.block_eq_of_survives_nd2_at_endpoint data fd hc hab hOne star
    _ (endpoint_above data hc hab hOne first.1) hFirstNd edge hSurvives hEdgeFirst
  have hSecondBlock := W4IncomingCensus.block_eq_of_survives_nd2_at_endpoint data fd hc hab hOne star
    _ (endpoint_above data hc hab hOne second.1) hSecondNd edge hSurvives hEdgeSecond
  have hMerged := block_eq_union_of_active_pair data fd hc hab hOne star block _ _ hActive
  rw [← hFirstBlock, ← hSecondBlock, Finset.union_self] at hMerged
  exact ⟨edge, hEdge, hMerged.symm, hFirstBlock.symm.trans hMerged.symm,
    hSecondBlock.symm.trans hMerged.symm⟩

/-- In the singleton/pair-side case, the small endpoint and internal edge
are the singleton-side retained class; the trivalent endpoint is the whole
merged class. This is the inclusion-and-union step of auxiliary r0-nd3. -/
theorem nd3_singleton_side_classes
    (hCompat : DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 3)
    (first second third : NonDanglingEdge (contractDatum data hc hab hOne)) (hNe : second ≠ third)
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 (mergedVertex data hc hab hOne block))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 (mergedVertex data hc hab hOne block))
    (hThird : Incident (contractDatum data hc hab hOne) third.1 (mergedVertex data hc hab hOne block))
    (hOpposite : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) first.1.1.1 ≠
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1)
    (hSame : star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) second.1.1.1 =
      star.right (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) third.1.1.1) :
    ∃ edge : data.SourceEdge,
      internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) = {edge} ∧
      (data.edgePartition edge.1.1).block edge.1.2 =
        ((contractDatum data hc hab hOne).edgePartition first.1.1.1).block first.1.1.2 ∧
      (data.vertexPartition (endpoint data hc hab hOne first.1).1.1).block
        (endpoint data hc hab hOne first.1).1.2 =
          ((contractDatum data hc hab hOne).edgePartition first.1.1.1).block first.1.1.2 ∧
      (data.vertexPartition (endpoint data hc hab hOne second.1).1.1).block
        (endpoint data hc hab hOne second.1).1.2 = (mergedPartition data a b).block block.1 := by
  classical
  obtain ⟨_, edge, hEdge, hActive, hEdgeFirst, hEdgeSecond, hFirstNd, _⟩ :=
    nd3_singleton_pairing_side data fd hc hab hOne star hCompat block hNd
      first second third hNe hFirst hSecond hThird hOpposite hSame
  have hMember : edge ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne block) := by
    rw [hEdge]; simp
  have hSurvives := ((mem_internalEdges data hc hab hOne _ edge).mp hMember).1
  have hSmall := W4IncomingCensus.block_eq_of_survives_nd2_at_endpoint data fd hc hab hOne star
    _ (endpoint_above data hc hab hOne first.1) hFirstNd edge hSurvives hEdgeFirst
  have hFirstBlock := endpoint_block_eq_flag data fd hc hab hOne star hCompat.1 block first hFirst hFirstNd
  have hSubset : (data.edgePartition edge.1.1).block edge.1.2 ⊆
      (data.vertexPartition (endpoint data hc hab hOne second.1).1.1).block
        (endpoint data hc hab hOne second.1).1.2 := by
    obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data edge _).mp hEdgeSecond
    intro sheet hSheet
    exact (SheetPartition.mem_block_iff _ _ _).mpr
      (hRel.trans ((refines_of_mem_incidentEdges data hAt).rel
        ((SheetPartition.mem_block_iff _ _ _).mp hSheet)))
  have hMerged := block_eq_union_of_active_pair data fd hc hab hOne star block _ _ hActive
  rw [← hSmall, Finset.union_eq_right.mpr hSubset] at hMerged
  exact ⟨edge, hEdge, hSmall.trans hFirstBlock, hFirstBlock, hMerged.symm⟩

end DraismaVargas.LocalCases.W4IncomingSheetClasses
