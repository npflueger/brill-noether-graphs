import DraismaVargas.LocalCases.W4IncomingRetainedFlags
import DraismaVargas.LocalCases.M11IncomingOuterPartitions

/-!
# Literal partitions at the normalized incoming W4 target

The W4 target isomorphism of the incoming normalization
(`W4IncomingTargetNormalization.targetIso`) fixes all outer partitions and sends the
contracted edge to the new column. At a canonical retained flag, its target
side pulls back to the canonical endpoint of the incoming datum, even when the target
normalization exchanges the two ends. These equalities concern the literal partitions
(representative tables); matching whole candidates up to `SheetPartition.SameBlocks`
needs, in addition, a census of sheet classes.  They are used in
`DraismaVargasCount.DiscreteW4Normalization`, where the contracted wall partition is
discrete and every local partition is forced.
-/

namespace DraismaVargas.LocalCases.W4IncomingNormalizedPartitions

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open TargetExpansion ContractionRamification W4StableSource FullDimensionalSource
open FullContractionFibre
open W4IncomingTargetNormalization W4IncomingRetainedFlags M11IncomingOuterPartitions

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

noncomputable abbrev transported :=
  GluingTransport.transport (targetIso data fd hc hab hOne star) data

/-- Every outer vertex keeps its exact old wall partition. -/
theorem vertexPartition_of_ne (vertex : (contract target hab hOne).V)
    (hOff : vertex ≠ ⟨a, hab⟩) :
    (transported data fd hc hab hOne star).vertexPartition
      (oldVertex (contract target hab hOne) vertex) =
      (contractDatum data hc hab hOne).vertexPartition vertex :=
  transported_vertexPartition_of_ne data hc hab hOne _
    (pairing_placement data fd hc hab hOne star) vertex hOff

/-- Every literal retained target column keeps its exact wall partition. -/
theorem edgePartition_retained (edge : (contract target hab hOne).edges) :
    (transported data fd hc hab hOne star).edgePartition
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (star.right (pairing data fd hc hab hOne star)) (some edge)) =
      (contractDatum data hc hab hOne).edgePartition edge :=
  transported_edgePartition_retained data hc hab hOne _
    (pairing_placement data fd hc hab hOne star) fd.targetConnected fd.targetGenus edge

/-- The restored column has precisely the original contracted-edge partition. -/
theorem edgePartition_new :
    (transported data fd hc hab hOne star).edgePartition
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (star.right (pairing data fd hc hab hOne star)) none) =
      data.edgePartition contracted :=
  transported_edgePartition_new data hc hab hOne _
    (pairing_placement data fd hc hab hOne star) fd.targetConnected fd.targetGenus

/-- The normalized side of a retained flag pulls back to its incoming
endpoint side. The possible global endpoint exchange cancels exactly. -/
theorem targetIso_symm_flag_side
    (block : (mergedPartition data a b).Blocks)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hIncident : Incident (contractDatum data hc hab hOne) edge
      (mergedVertex data hc hab hOne block)) :
    (targetIso data fd hc hab hOne star).vertexEquiv.symm
      (if star.right (pairing data fd hc hab hOne star) edge.1.1 then
        freshVertex (contract target hab hOne)
       else oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      (endpoint data hc hab hOne edge).1.1 := by
  classical
  have hAt := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne)
    edge (mergedVertex data hc hab hOne block)).mp hIncident).1
  have hPair := incomingIso_symm_endpoints hc hab hOne _
    (pairing_placement data fd hc hab hOne star)
  change ((targetIso data fd hc hab hOne star).vertexEquiv.symm
      (oldVertex (contract target hab hOne) ⟨a, hab⟩),
    (targetIso data fd hc hab hOne star).vertexEquiv.symm
      (freshVertex (contract target hab hOne))) = _ at hPair
  by_cases hSupport : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne e = star.right (pairing data fd hc hab hOne star) e
  · rw [if_pos hSupport] at hPair
    have hLeft := congrArg Prod.fst hPair
    have hRight := congrArg Prod.snd hPair
    have hSide := hSupport edge.1.1 hAt
    rw [endpoint_target, hSide]
    cases hBit : star.right (pairing data fd hc hab hOne star) edge.1.1 <;>
      simp only [Bool.false_eq_true, reduceIte] <;> assumption
  · rw [if_neg hSupport] at hPair
    have hLeft := congrArg Prod.fst hPair
    have hRight := congrArg Prod.snd hPair
    have hOpposite := (pairing_placement data fd hc hab hOne star).resolve_left hSupport
    have hSide := hOpposite edge.1.1 hAt
    rw [endpoint_target, hSide]
    cases hBit : star.right (pairing data fd hc hab hOne star) edge.1.1 <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, reduceIte] <;>
      assumption

/-- Literal endpoint partition equality at any retained wall flag of the incoming
datum.  No choice of representative or active endpoint is added as input. -/
theorem vertexPartition_flag_side
    (block : (mergedPartition data a b).Blocks)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hIncident : Incident (contractDatum data hc hab hOne) edge
      (mergedVertex data hc hab hOne block)) :
    (transported data fd hc hab hOne star).vertexPartition
      (if star.right (pairing data fd hc hab hOne star) edge.1.1 then
        freshVertex (contract target hab hOne)
       else oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (endpoint data hc hab hOne edge).1.1 :=
  congrArg data.vertexPartition (targetIso_symm_flag_side data fd hc hab hOne star block edge hIncident)

end DraismaVargas.LocalCases.W4IncomingNormalizedPartitions
