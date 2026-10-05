module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
public import DraismaVargas.LocalCases.W4IncomingRetainedFlags
public import DraismaVargas.LocalCases.SingleRowForest
public import DraismaVargas.LocalCases.WallAdmissibility

@[expose] public section

/-!
# The actual valency-four anchor at a one-row wall

Source: Vargas, Part II, Section 5.2, case `{v4-nd4}`.  The four
surviving wall flags lie over distinct target occurrences because they lift to
the two change-zero trivalent endpoints of the incoming full-dimensional
datum.  At each endpoint the local `r0-nd3` calculation is target-injective;
the pruned-fibre census says that two lifted flags on the same target side
meet the same incoming source vertex.

Thus wall valency four and `nd(A)=4` do not by themselves supply the
classifier.  The missing source input is precisely the incoming
full-dimensional presentation together with preservation of danglingness.
At an actual one-zero-row wall, the non-loop row proves a contraction forest,
and the forest theorem supplies this preservation.  No active-label
or direction-injectivity receipt is assumed below.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourAnchor

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration PrunedFibreValency PrunedFibreTree
open FullDimensionalSource
open W4Assembly
open FullContractionFibre

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

section Incoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

local notation "M₀" => contractDatum data hc hab hOne

include fd

/-- An incoming full-dimensional datum makes the target direction injective
on the surviving neighbourhood of every block over the four-valent wall. -/
theorem targetInjective
    (hPreserved : DanglingPreserved data hc hab hOne)
    (anchor : WallBlock M₀ ⟨a, hab⟩) :
    NonDanglingStarInjective M₀ star anchor := by
  let block : (mergedPartition data a b).Blocks := ⟨anchor.1, by
    simpa only [contractDatum_vertexPartition_merge] using anchor.2⟩
  have hVertex : WallBlock.sourceVertex M₀ ⟨a, hab⟩ anchor =
      mergedVertex data hc hab hOne block := by
    apply Subtype.ext
    exact Prod.ext rfl anchor.2
  constructor
  intro label first second hFirstBlock hSecondBlock hFirstTarget hSecondTarget
    hFirstSurvives hSecondSurvives
  let firstWall : NonDanglingEdge M₀ := ⟨first, hFirstSurvives⟩
  let secondWall : NonDanglingEdge M₀ := ⟨second, hSecondSurvives⟩
  have hFirstIncident : Incident M₀ first (mergedVertex data hc hab hOne block) := by
    rw [← hVertex]
    apply (incident_wallBlock_sourceVertex_iff M₀ anchor first).2
    exact ⟨by rw [hFirstTarget]; exact star.edge_mem_incidentEdges label,
      hFirstBlock⟩
  have hSecondIncident : Incident M₀ second (mergedVertex data hc hab hOne block) := by
    rw [← hVertex]
    apply (incident_wallBlock_sourceVertex_iff M₀ anchor second).2
    exact ⟨by rw [hSecondTarget]; exact star.edge_mem_incidentEdges label,
      hSecondBlock⟩
  have hFirstActive := W4IncomingRetainedFlags.endpoint_active data hc hab hOne
    hPreserved block firstWall hFirstIncident
  have hSecondActive := W4IncomingRetainedFlags.endpoint_active data hc hab hOne
    hPreserved block secondWall hSecondIncident
  have hWallTarget : first.1.1 = second.1.1 :=
    hFirstTarget.trans hSecondTarget.symm
  have hEndpointSide :
      (W4IncomingRetainedFlags.endpoint data hc hab hOne first).1.1 =
        (W4IncomingRetainedFlags.endpoint data hc hab hOne second).1.1 := by
    apply (W4IncomingRetainedFlags.endpoint_target_eq_iff data hc hab hOne first second).2
    exact congrArg (IncomingTargetExpansion.right hc hab hOne) hWallTarget
  have hEndpoint :
      W4IncomingRetainedFlags.endpoint data hc hab hOne first =
        W4IncomingRetainedFlags.endpoint data hc hab hOne second :=
    W4IncomingSideCensus.eq_of_same_side data fd hc hab hOne star _ _ _
      hFirstActive hSecondActive hEndpointSide
  have hFirstUpIncident := W4IncomingRetainedFlags.endpoint_incident data hc hab hOne
    block first hFirstIncident
  have hSecondUpIncident : Incident data (sourceEdgeEmbedding data hc hab hOne second)
      (W4IncomingRetainedFlags.endpoint data hc hab hOne first) := by
    rw [hEndpoint]
    exact W4IncomingRetainedFlags.endpoint_incident data hc hab hOne
      block second hSecondIncident
  have hAbove :
      (W4IncomingRetainedFlags.endpoint data hc hab hOne first).1.1 = a ∨
        (W4IncomingRetainedFlags.endpoint data hc hab hOne first).1.1 = b := by
    rw [W4IncomingRetainedFlags.endpoint_target]
    split <;> simp
  have hTargetUp :
      (sourceEdgeEmbedding data hc hab hOne first).1.1 =
        (sourceEdgeEmbedding data hc hab hOne second).1.1 := by
    have hFirstVal := IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne first
    have hSecondVal := IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne second
    rw [congrArg Prod.fst hFirstVal, congrArg Prod.fst hSecondVal]
    exact congrArg (unfoldEdge hc hab hOne) hWallTarget
  apply (sourceEdgeEmbedding data hc hab hOne).injective
  exact W4IncomingCensus.sourceEdge_eq_of_same_target_at_endpoint data fd hc hab hOne star
    _ hAbove _ _ (nonDanglingEmbedding data hPreserved firstWall).2
    (nonDanglingEmbedding data hPreserved secondWall).2 hFirstUpIncident hSecondUpIncident
    hTargetUp

/-- The actual producer for the Part II `{v4-nd4}` classifier. The wall count
`nd(A)=4` forces all four labels only after incoming full-dimensionality has
supplied target-direction injectivity. -/
theorem fourBranchAnchor
    (hPreserved : DanglingPreserved data hc hab hOne)
    (anchor : WallBlock M₀ ⟨a, hab⟩)
    (hNd : nonDanglingValency M₀
      (WallBlock.sourceVertex M₀ ⟨a, hab⟩ anchor) = 4) :
    NonTrivalentValencyFourKZero.FourBranchAnchor M₀ star anchor := by
  have hInjective := targetInjective data fd hc hab hOne star hPreserved anchor
  refine ⟨?_, hInjective⟩
  apply Finset.eq_univ_of_card
  rw [card_activeLabels_eq_nonDanglingValency M₀ star anchor hInjective, hNd]
  decide +kernel

/-- The forest produced by a legal wall contraction supplies the only
danglingness transfer needed by `fourBranchAnchor`. -/
theorem fourBranchAnchor_of_contractionForest
    (hForest : ContractionForest data a b contracted)
    (anchor : WallBlock M₀ ⟨a, hab⟩)
    (hNd : nonDanglingValency M₀
      (WallBlock.sourceVertex M₀ ⟨a, hab⟩ anchor) = 4) :
    NonTrivalentValencyFourKZero.FourBranchAnchor M₀ star anchor :=
  fourBranchAnchor data fd hc hab hOne star
    (WallAdmissibility.danglingPreserved_of_contractionForest
      data hc hab hOne hForest) anchor hNd

/-- The direct one-zero-row producer used at a Part II open facet. The
non-loop simple end proves that the zero source subgraph is a forest; no
direction-injectivity or active-label receipt is supplied. -/
theorem fourBranchAnchor_of_single_zero_row
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZero : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (anchor : WallBlock M₀ ⟨a, hab⟩)
    (hNd : nonDanglingValency M₀
      (WallBlock.sourceVertex M₀ ⟨a, hab⟩ anchor) = 4) :
    NonTrivalentValencyFourKZero.FourBranchAnchor M₀ star anchor :=
  fourBranchAnchor_of_contractionForest data fd hc hab hOne star
    (SingleRowForest.contractionForest_of_single_row fd.labelling coordinates
      hNonnegative facet hRows hEnd hc hZero) anchor hNd

end Incoming

end DraismaVargas.LocalCases.NonTrivalentValencyFourAnchor
