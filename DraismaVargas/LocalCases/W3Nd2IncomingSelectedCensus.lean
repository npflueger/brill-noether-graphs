import DraismaVargas.LocalCases.W3Nd2IncomingDirection
import DraismaVargas.LocalCases.PrunedDivalentFibre
import DraismaVargas.LocalCases.W4IncomingRetainedFlags
import DraismaVargas.LocalCases.W4IncomingClassUnion
import DraismaVargas.LocalCases.M11IncomingPartitions

/-!
# The selected incoming fibre in the W3 nd2 case

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd2}` and Figure 31, whose incoming uniqueness refers back to the
analogous argument of Case `{w3-r1-nd3-t2}`.

The two named surviving wall occurrences of the selected `Nd2Profile` lie on
opposite restored target sides.  The direction exclusion
`W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large` places the
isolated divalent direction at SMALL or LARGE; in either case the matching
Figure 31 candidate's own side predicate separates the two occurrences, and
the incoming placement agrees with it up to the global endpoint swap.  Their
canonical same-sheet endpoints are therefore two distinct active constituents
of the selected pruned fibre.  The pruned-tree count and
`PrunedDivalentFibre.internalEdges_card_le_one` then force that fibre to be
exactly one surviving contracted occurrence joining two divalent endpoints.

That census is all this file proves.  The selected endpoint and internal
sheet classes of Figure 31, the r0 background blocks, and the
stored-representative matching through `PartitionNormalization` are built on
top of it elsewhere (`W3Nd2IncomingMemberMatching`).
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingSelectedCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion TargetExpansion
open PrunedFibreValency PrunedFibreTree PrunedDivalentFibre
open FullContractionFibre
open W4IncomingRetainedFlags W4IncomingClassUnion
open M11IncomingPartitions
open W3Nd2SourceCandidates W3Nd2FineRefinement W3Nd2FineCandidates
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

noncomputable abbrev selectedVertex
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    (contractDatum data hc hab hOne).SourceVertex :=
  WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
    input.distinguishedBlock

noncomputable def selectedBlock
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    (mergedPartition data a b).Blocks :=
  ⟨input.distinguishedBlock.1, by
    simpa only [contractDatum_vertexPartition_merge] using
      input.distinguishedBlock.2⟩

theorem selectedVertex_eq_mergedVertex
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    selectedVertex data hc hab hOne star input =
      mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · dsimp only [selectedVertex, WallBlock.sourceVertex, GluingDatum.sourceEndpoint,
      mergedVertex, selectedBlock]
    exact input.distinguishedBlock.2

noncomputable abbrev smallEndpoint
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) : data.SourceVertex :=
  endpoint data hc hab hOne profile.small.1

noncomputable abbrev largeEndpoint
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) : data.SourceVertex :=
  endpoint data hc hab hOne profile.large.1

section Wrappers

variable {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall}

/-- The coarse Figure 31 candidate carries exactly the smaller direction's
side predicate.  Stated as an explicitly instantiable term equality: at the
contracted wall `⟨a, hab⟩` the surrounding expression is not type-correct at
`implicit` transparency, so `rw`/`simp only` on this wrapper cannot fire and
the equation must be consumed by `Eq.trans`. -/
theorem coarseCandidate_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (edge : target.edges) :
    (coarseCandidate input profile).right edge = rightOf (smallTarget input profile) edge :=
  rfl

/-- The oppositely oriented fine Figure 31 candidate carries the larger
direction's side predicate.  Consume it by `Eq.trans`, as above. -/
theorem fineCandidate_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (edge : target.edges) :
    (fineCandidate input profile).right edge = rightOf (largeTarget input profile) edge :=
  rfl

/-- The coarse candidate separates the two surviving directions. -/
theorem coarse_right_ne (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (coarseCandidate input profile).right (smallTarget input profile) ≠
      (coarseCandidate input profile).right (largeTarget input profile) := by
  have hSelf : rightOf (smallTarget input profile) (smallTarget input profile) = false := by
    simp [rightOf]
  have hOther : rightOf (smallTarget input profile) (largeTarget input profile) = true := by
    simp [rightOf, profile.target_ne.symm]
  intro hEq
  have hFalse : (false : Bool) = true :=
    hSelf.symm.trans
      (((coarseCandidate_right input profile (smallTarget input profile)).symm.trans hEq).trans
        ((coarseCandidate_right input profile (largeTarget input profile)).trans hOther))
  exact Bool.noConfusion hFalse

/-- The fine candidate separates the two surviving directions. -/
theorem fine_right_ne (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineCandidate input profile).right (smallTarget input profile) ≠
      (fineCandidate input profile).right (largeTarget input profile) := by
  have hOther : rightOf (largeTarget input profile) (smallTarget input profile) = true := by
    simp [rightOf, profile.target_ne]
  have hSelf : rightOf (largeTarget input profile) (largeTarget input profile) = false := by
    simp [rightOf]
  intro hEq
  have hFalse : (true : Bool) = false :=
    hOther.symm.trans
      (((fineCandidate_right input profile (smallTarget input profile)).symm.trans hEq).trans
        ((fineCandidate_right input profile (largeTarget input profile)).trans hSelf))
  exact Bool.noConfusion hFalse

end Wrappers

/-- The two surviving directions of the selected nd2 profile are restored to
opposite original endpoints of the contracted edge. -/
theorem small_large_side_ne
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hDirection : divalentOccurrence data hc hab hOne fullDim star =
        smallTarget input profile ∨
      divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile) :
    IncomingTargetExpansion.right hc hab hOne profile.small.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne profile.large.1.1.1 := by
  rcases hDirection with hSmall | hLarge
  · have hCandidateNe := coarse_right_ne input profile
    rcases coarse_placement_of_eq_small data hc hab hOne fullDim star input profile hSmall with
      hPlacement | hPlacement
    · intro hEqual
      exact hCandidateNe
        (((hPlacement _ (smallTarget_mem input profile)).symm.trans hEqual).trans
          (hPlacement _ (largeTarget_mem input profile)))
    · intro hEqual
      apply hCandidateNe
      have hNotEqual := (hPlacement _ (smallTarget_mem input profile)).symm.trans
        (hEqual.trans (hPlacement _ (largeTarget_mem input profile)))
      exact Bool.not_inj hNotEqual
  · have hCandidateNe := fine_right_ne input profile
    rcases fine_placement_of_eq_large data hc hab hOne fullDim star input profile hLarge with
      hPlacement | hPlacement
    · intro hEqual
      exact hCandidateNe
        (((hPlacement _ (smallTarget_mem input profile)).symm.trans hEqual).trans
          (hPlacement _ (largeTarget_mem input profile)))
    · intro hEqual
      apply hCandidateNe
      have hNotEqual := (hPlacement _ (smallTarget_mem input profile)).symm.trans
        (hEqual.trans (hPlacement _ (largeTarget_mem input profile)))
      exact Bool.not_inj hNotEqual

/-- Exact pruned topology of the selected incoming fibre.

The hypotheses are jointly satisfiable: they are exactly the bundle already
consumed by the checked `W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large`
and `exists_coarse_or_fine_normalization`, namely an actual full-dimensional
incoming presentation whose contraction of the single edge `contracted`
between `a` and `b` is a forest with dangling compatibility, a genuine
trivalent star at the contracted wall, a W3 source input for it, and a
Figure 31 nd2 profile of its distinguished block.  Nothing here forces the
two surviving directions to coincide or the fibre to be empty; the
conclusion is a topology statement about an inhabited fibre. -/
theorem selected_fibre_census
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd2Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {smallEndpoint data hc hab hOne star input profile,
          largeEndpoint data hc hab hOne star input profile} ∧
      Incident data internal (smallEndpoint data hc hab hOne star input profile) ∧
      Incident data internal (largeEndpoint data hc hab hOne star input profile) ∧
      nonDanglingValency data (smallEndpoint data hc hab hOne star input profile) = 2 ∧
      nonDanglingValency data (largeEndpoint data hc hab hOne star input profile) = 2 := by
  classical
  let vertex := selectedVertex data hc hab hOne star input
  let block := selectedBlock data hc hab hOne star input
  let small : NonDanglingEdge (contractDatum data hc hab hOne) :=
    ⟨profile.small.1, profile.small_survives⟩
  let large : NonDanglingEdge (contractDatum data hc hab hOne) :=
    ⟨profile.large.1, profile.large_survives⟩
  have hSmallActive : smallEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne vertex := by
    have hInc : Incident (contractDatum data hc hab hOne) profile.small.1
        (mergedVertex data hc hab hOne block) := by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.small.2
    have h := W4IncomingRetainedFlags.endpoint_active data hc hab hOne hCompat.1
      block small hInc
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input] at h
    exact h
  have hLargeActive : largeEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne vertex := by
    have hInc : Incident (contractDatum data hc hab hOne) profile.large.1
        (mergedVertex data hc hab hOne block) := by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.large.2
    have h := W4IncomingRetainedFlags.endpoint_active data hc hab hOne hCompat.1
      block large hInc
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input] at h
    exact h
  have hDirection := divalentOccurrence_eq_small_or_large data hc hab hOne fullDim
    hForest hCompat star input profile
  have hTargetNe :
      (smallEndpoint data hc hab hOne star input profile).1.1 ≠
        (largeEndpoint data hc hab hOne star input profile).1.1 := by
    have hSideNe := small_large_side_ne data hc hab hOne fullDim star input profile hDirection
    rw [endpoint_target, endpoint_target]
    cases hSmallSide : IncomingTargetExpansion.right hc hab hOne profile.small.1.1.1 <;>
      cases hLargeSide : IncomingTargetExpansion.right hc hab hOne profile.large.1.1.1 <;>
      simp_all [Ne.symm hab]
  have hEndpointNe : smallEndpoint data hc hab hOne star input profile ≠
      largeEndpoint data hc hab hOne star input profile := fun h ↦
    hTargetNe (congrArg (fun point : data.SourceVertex ↦ point.1.1) h)
  have hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty :=
    ⟨_, hSmallActive⟩
  -- `internalEdges_card_add_one_eq_activeFibreVertices_card` is stated at
  -- `mergedVertex ... block`; ascribe the result to the local abbreviation so
  -- that `omega` below sees a single active-fibre cardinality atom.
  have hTree : (internalEdges data hc hab hOne vertex).card + 1 =
      (activeFibreVertices data hc hab hOne vertex).card := by
    have h := internalEdges_card_add_one_eq_activeFibreVertices_card
      data hc hab hOne hForest block (by
        simpa only [vertex, selectedVertex_eq_mergedVertex data hc hab hOne star input]
          using hNonempty)
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input] at h
    exact h
  have hInternalLe := internalEdges_card_le_one data hc hab hOne fullDim hCompat hForest
    (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
    (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
    vertex profile.valency
  have hActiveLower : 2 ≤ (activeFibreVertices data hc hab hOne vertex).card := by
    have hPair : ({smallEndpoint data hc hab hOne star input profile,
        largeEndpoint data hc hab hOne star input profile} : Finset data.SourceVertex) ⊆
        activeFibreVertices data hc hab hOne vertex := by
      intro point hPoint
      rcases Finset.mem_insert.mp hPoint with rfl | hPoint
      · exact hSmallActive
      · exact (Finset.mem_singleton.mp hPoint) ▸ hLargeActive
    simpa [Finset.card_pair hEndpointNe] using Finset.card_le_card hPair
  have hInternalCard : (internalEdges data hc hab hOne vertex).card = 1 := by omega
  obtain ⟨internal, hInternal⟩ := Finset.card_eq_one.mp hInternalCard
  have hInternalMem : internal ∈ internalEdges data hc hab hOne vertex := by
    rw [hInternal]
    simp
  have hActiveCard : (activeFibreVertices data hc hab hOne vertex).card = 2 := by omega
  have hActive : activeFibreVertices data hc hab hOne vertex =
      {smallEndpoint data hc hab hOne star input profile,
        largeEndpoint data hc hab hOne star input profile} := by
    apply Finset.eq_of_subset_of_card_le
    · intro point hPoint
      have hInc := internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim
        hCompat hForest
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        vertex profile.valency internal hInternalMem point hPoint
      have hSmallInc := internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim
        hCompat hForest
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        vertex profile.valency internal hInternalMem _ hSmallActive
      have hLargeInc := internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim
        hCompat hForest
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
        vertex profile.valency internal hInternalMem _ hLargeActive
      rcases hInc with hInc | hInc <;> rcases hSmallInc with hSmallInc | hSmallInc <;>
        rcases hLargeInc with hLargeInc | hLargeInc
      all_goals simp_all
    · rw [hActiveCard, Finset.card_pair hEndpointNe]
  have hSmallNd := nonDanglingValency_eq_two_of_mem_activeFibre data hc hab hOne
    fullDim.valid.1 hCompat hForest block (by
      simpa only [selectedVertex_eq_mergedVertex data hc hab hOne star input] using profile.valency) _
      (by simpa only [vertex, selectedVertex_eq_mergedVertex data hc hab hOne star input] using
        hSmallActive)
  have hLargeNd := nonDanglingValency_eq_two_of_mem_activeFibre data hc hab hOne
    fullDim.valid.1 hCompat hForest block (by
      simpa only [selectedVertex_eq_mergedVertex data hc hab hOne star input] using profile.valency) _
      (by simpa only [vertex, selectedVertex_eq_mergedVertex data hc hab hOne star input] using
        hLargeActive)
  refine ⟨internal, hInternal, hActive, ?_, ?_, hSmallNd, hLargeNd⟩
  · exact internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim hCompat hForest
      (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
      (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
      vertex profile.valency internal hInternalMem _ hSmallActive
  · exact internalEdge_incident_of_mem_activeFibre data hc hab hOne fullDim hCompat hForest
      (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
      (by rcases endpoint_valencies data hc hab hOne fullDim star with h | h <;> omega)
      vertex profile.valency internal hInternalMem _ hLargeActive

end DraismaVargas.LocalCases.W3Nd2IncomingSelectedCensus
