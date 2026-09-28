import DraismaVargas.LocalCases.W3Nd2IncomingSelectedCensus

/-!
# Figure 31 sheet classes at the selected incoming W3 nd2 fibre

Source: Draisma--Vargas Part I, case `w3-r1-nd2` and Figure 31, whose argument
refers to a reasoning analogous to case `w3-nd3-t2`.  That reference is read
here as case `{w3-r1-nd3-t2}`, and that is the argument transcribed here.

The paper's sentence is: *the vertices of `ndG^q_{A_0}` above `v` belong to
Case (r0-nd2) of the local properties, and the ones above `u` to Case (r1-nd2)*.
In this development `W3Nd2IncomingTargetPlacement.endpoint_valencies` is exactly
that split: one original endpoint of the contracted occurrence is divalent and
carries the whole unit of target change, the other is trivalent and has zero
target change, hence zero local ramification above it.

So the fibre census of `W3Nd2IncomingSelectedCensus.selected_fibre_census` --
one internal occurrence joining two divalent active endpoints -- is refined by:

* the **unramified** endpoint (the one over the trivalent original endpoint) is
  Case (r0-nd2), so its literal sheet class equals the class of *every*
  surviving occurrence at it: the internal occurrence, and the retained wall
  flag it keeps.  This is the `w3-r1-nd3-t2` step "as subsets of `[d]`, the
  edges `e'`, `e_β^{(q)}` and their common end are equal";
* **refinement across the internal occurrence** then fixes the ramified
  endpoint: the internal class sits inside the ramified endpoint's class, so
  the non-dangling union `A_0 = A^{(q)} ∪ A'` collapses to `A_0 = A^{(q)}`.
  This is Position II.a's "`A_0 = A^{(q)} ∪ A' = A^{(q)}`".

Which of the two named Figure 31 survivors carries the ramified endpoint is a
genuine dichotomy -- it is what distinguishes `M^{(1)}` from `M^{(2)}` -- so it
is carried as a hypothesis, discharged into a disjunction at the end by
`W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large`.

The non-dangling union (Part I's `lemma-class-union`) is
`W4IncomingClassUnion.AnyWall.block_eq_active_union`, stated without a
`FourStar` hypothesis: zero local ramification at an inactive endpoint comes
from `StableLocalProperties.localRamification_eq_zero_of_forall_isDangling`,
which needs only the full-dimensional presentation.  The two `_local`
declarations below are one-line wrappers of the `AnyWall` statements, named for
their callers `W3Nd2IncomingBackground` and `W3Nd3IncomingCensus`.  Matching
these classes against the stored representatives of the Figure 31 candidates,
and the r0 background blocks, are separate steps and are not attempted here.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingSheetClasses

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion TargetExpansion
open PrunedFibreValency PrunedFibreTree PrunedDivalentFibre
open FullContractionFibre
open W4IncomingRetainedFlags
open W3Nd2SourceCandidates W3Nd2FineRefinement W3Nd2FineCandidates
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection W3Nd2IncomingSelectedCensus

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

section Union

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fullDim

/-- An endpoint block meeting no surviving occurrence is a literal singleton.

This is `W4IncomingClassUnion.AnyWall.inactive_endpoint_block`, stated without
the W4 `FourStar`: a source vertex all of whose incident occurrences are
dangling is unramified by
`StableLocalProperties.localRamification_eq_zero_of_forall_isDangling`, which
needs only the full-dimensional presentation.  This local name is used by
`W3Nd2IncomingBackground`. -/
theorem inactive_endpoint_block_local (place : target.V) (sheet : Fin degree)
    (hZero : nonDanglingValency data (data.sourceEndpoint place sheet) = 0) :
    (data.vertexPartition place).block sheet = {sheet} :=
  W4IncomingClassUnion.AnyWall.inactive_endpoint_block data fullDim place sheet hZero

/-- The literal non-dangling union of Part I's `lemma-class-union` at a W3 wall.

This is `W4IncomingClassUnion.AnyWall.block_eq_active_union`, stated without
the W4 `FourStar`; this local name is used by `W3Nd3IncomingCensus`. -/
theorem block_eq_active_union_local (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    (mergedPartition data a b).block block.1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).biUnion
        (fun point ↦ (data.vertexPartition point.1.1).block point.1.2) :=
  W4IncomingClassUnion.AnyWall.block_eq_active_union data fullDim hc hab hOne block hNonempty

end Union


section LocalProperties

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fullDim

omit hc hab hOne in
/-- The paper's Case (r0-nd2) side: a source vertex over an original endpoint
of zero target change is unramified. -/
theorem localRamification_endpoint_eq_zero (vertex : data.SourceVertex)
    (place : target.V) (hAbove : vertex.1.1 = place)
    (hChange : data.targetChange place = 0) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 :=
  W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fullDim vertex
    (by rw [hAbove]; exact hChange)

/-- Case (r0-nd2) at a divalent unramified canonical endpoint: its sheet class
is literally the retained wall occurrence's class.  This is the W3 analogue of
`W4IncomingSheetClasses.endpoint_block_eq_flag`, with the vanishing of the
local ramification supplied by the endpoint's target change rather than by a
four-valent wall. -/
theorem endpoint_block_eq_flag_local
    (hPreserved : DanglingPreserved data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (edge : NonDanglingEdge (contractDatum data hc hab hOne))
    (hIncident : Incident (contractDatum data hc hab hOne) edge.1
      (mergedVertex data hc hab hOne block))
    (hNd : nonDanglingValency data (endpoint data hc hab hOne edge.1) = 2)
    (hChange : data.targetChange (endpoint data hc hab hOne edge.1).1.1 = 0) :
    (data.vertexPartition (endpoint data hc hab hOne edge.1).1.1).block
        (endpoint data hc hab hOne edge.1).1.2 =
      ((contractDatum data hc hab hOne).edgePartition edge.1.1.1).block edge.1.1.2 := by
  have hRam := localRamification_endpoint_eq_zero data fullDim
    (endpoint data hc hab hOne edge.1) _ rfl hChange
  have h := W4IncomingCensus.block_eq_of_survives_nd2_r0 data fullDim.danglingEdgeNoGlue
    (endpoint data hc hab hOne edge.1) hNd hRam
    (nonDanglingEmbedding data hPreserved edge).1
    (nonDanglingEmbedding data hPreserved edge).2
    (endpoint_incident data hc hab hOne block edge.1 hIncident)
  exact h.symm.trans (embedding_block data hc hab hOne edge.1)

/-- The two Figure 31 steps at one active pair.  The unramified endpoint fixes
the internal occurrence's class (Case (r0-nd2)); refinement of the internal
occurrence into the other endpoint then collapses the non-dangling union
`A_0 = A^{(q)} ∪ A'` onto the ramified endpoint. -/
theorem sheet_classes_of_active_pair
    (block : (mergedPartition data a b).Blocks)
    (internal : data.SourceEdge)
    (ramified unramified : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) =
      {ramified, unramified})
    (hInternal : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hRamIncident : Incident data internal ramified)
    (hUnramIncident : Incident data internal unramified)
    (hNd : nonDanglingValency data unramified = 2)
    (hChange : data.targetChange unramified.1.1 = 0) :
    (data.edgePartition internal.1.1).block internal.1.2 =
        (data.vertexPartition unramified.1.1).block unramified.1.2 ∧
      (data.vertexPartition ramified.1.1).block ramified.1.2 =
        (mergedPartition data a b).block block.1 := by
  classical
  have hSurvives := ((mem_internalEdges data hc hab hOne _ internal).mp hInternal).1
  have hRam := localRamification_endpoint_eq_zero data fullDim unramified _ rfl hChange
  have hInternalBlock := W4IncomingCensus.block_eq_of_survives_nd2_r0 data
    fullDim.danglingEdgeNoGlue unramified hNd hRam internal hSurvives hUnramIncident
  have hUnion := W4IncomingClassUnion.AnyWall.block_eq_union_of_active_pair data fullDim
    hc hab hOne block ramified unramified hActive
  have hSubset : (data.edgePartition internal.1.1).block internal.1.2 ⊆
      (data.vertexPartition ramified.1.1).block ramified.1.2 := by
    obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data internal _).mp hRamIncident
    intro sheet hSheet
    exact (SheetPartition.mem_block_iff _ _ _).mpr
      (hRel.trans ((refines_of_mem_incidentEdges data hAt).rel
        ((SheetPartition.mem_block_iff _ _ _).mp hSheet)))
  refine ⟨hInternalBlock, ?_⟩
  rw [← hInternalBlock, Finset.union_eq_left.mpr hSubset] at hUnion
  exact hUnion.symm

end LocalProperties


section Placement

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- A canonical endpoint restored to the right side lies over `b`. -/
theorem endpoint_target_of_true (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hSide : IncomingTargetExpansion.right hc hab hOne edge.1.1 = true) :
    (endpoint data hc hab hOne edge).1.1 = b := by
  rw [endpoint_target, hSide]
  simp

/-- A canonical endpoint restored to the left side lies over `a`. -/
theorem endpoint_target_of_false (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hSide : IncomingTargetExpansion.right hc hab hOne edge.1.1 = false) :
    (endpoint data hc hab hOne edge).1.1 = a := by
  rw [endpoint_target, hSide]
  simp

include fullDim

/-- **The paper's `u`/`v` split, read on the actual incoming datum.**  The
unique retained wall direction at the divalent original endpoint carries the
whole unit of target change (Case (r1-nd2)); a direction restored to the other
side lands on the trivalent original endpoint, whose target change vanishes, so
its canonical endpoint is unramified (Case (r0-nd2)). -/
theorem targetChange_endpoint_eq_zero_of_side_ne
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hNe : IncomingTargetExpansion.right hc hab hOne edge.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star)) :
    data.targetChange (endpoint data hc hab hOne edge).1.1 = 0 := by
  have hSpec := (divalentOccurrence_spec data hc hab hOne fullDim star).2
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨_, hB, _, hChange⟩ | ⟨hA, _, hChange, _⟩
  · have hFalse : IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) = false := by
      rcases hSpec with hLeft | hRight
      · exact hLeft.2
      · omega
    rw [hFalse] at hNe
    have hTrue : IncomingTargetExpansion.right hc hab hOne edge.1.1 = true := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne edge.1.1
      · exact absurd hValue hNe
      · rfl
    rw [endpoint_target_of_true data hc hab hOne edge hTrue]
    exact hChange
  · have hTrue : IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) = true := by
      rcases hSpec with hLeft | hRight
      · omega
      · exact hRight.2
    rw [hTrue] at hNe
    have hFalse : IncomingTargetExpansion.right hc hab hOne edge.1.1 = false := by
      cases hValue : IncomingTargetExpansion.right hc hab hOne edge.1.1
      · rfl
      · exact absurd hValue hNe
    rw [endpoint_target_of_false data hc hab hOne edge hFalse]
    exact hChange

end Placement

section WallClass

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The merged sheet class of a block is literally the contracted wall vertex's
own sheet class. -/
theorem mergedVertex_block (block : (mergedPartition data a b).Blocks) :
    ((contractDatum data hc hab hOne).vertexPartition
        (mergedVertex data hc hab hOne block).1.1).block
        (mergedVertex data hc hab hOne block).1.2 =
      (mergedPartition data a b).block block.1 := by
  show ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block block.1 = _
  rw [contractDatum_vertexPartition_merge]

/-- Hence `A_0` in the paper's notation: the merged class of the selected block
is the sheet class of the selected contracted wall vertex. -/
theorem selectedVertex_block
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    ((contractDatum data hc hab hOne).vertexPartition
        (selectedVertex data hc hab hOne star input).1.1).block
        (selectedVertex data hc hab hOne star input).1.2 =
      (mergedPartition data a b).block (selectedBlock data hc hab hOne star input).1 := by
  rw [selectedVertex_eq_mergedVertex data hc hab hOne star input]
  exact mergedVertex_block data hc hab hOne _

end WallClass


section Selected

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd2Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include fullDim hForest hCompat

/-- **Figure 31, `M^{(1)}`-orientation.**  If the divalent original endpoint is
restored to the *smaller* of the two named survivors, then the larger survivor's
canonical endpoint is the unramified one.  Its literal sheet class is the class
of the internal occurrence and of its own retained wall flag, and the smaller
survivor's endpoint carries the whole merged wall class `A_0`.

The hypothesis bundle is the one already shown jointly satisfiable by
`W3Nd2IncomingSelectedCensus.selected_fibre_census`; `hSmall` is one of the two
alternatives of `W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large`,
both of which genuinely occur (they are `M^{(1)}` and `M^{(2)}`). -/
theorem selected_sheet_classes_of_small
    (hSmall : divalentOccurrence data hc hab hOne fullDim star = smallTarget input profile) :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {smallEndpoint data hc hab hOne star input profile,
          largeEndpoint data hc hab hOne star input profile} ∧
      Incident data internal (smallEndpoint data hc hab hOne star input profile) ∧
      Incident data internal (largeEndpoint data hc hab hOne star input profile) ∧
      (data.edgePartition internal.1.1).block internal.1.2 =
        (data.vertexPartition
            (largeEndpoint data hc hab hOne star input profile).1.1).block
          (largeEndpoint data hc hab hOne star input profile).1.2 ∧
      (data.vertexPartition
            (largeEndpoint data hc hab hOne star input profile).1.1).block
          (largeEndpoint data hc hab hOne star input profile).1.2 =
        ((contractDatum data hc hab hOne).edgePartition
            (largeTarget input profile)).block profile.large.1.1.2 ∧
      (data.vertexPartition
            (smallEndpoint data hc hab hOne star input profile).1.1).block
          (smallEndpoint data hc hab hOne star input profile).1.2 =
        (mergedPartition data a b).block (selectedBlock data hc hab hOne star input).1 := by
  classical
  obtain ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, _, hLargeNd⟩ :=
    selected_fibre_census data hc hab hOne fullDim hForest hCompat star input profile
  have hSideNe := small_large_side_ne data hc hab hOne fullDim star input profile (Or.inl hSmall)
  have hNe : IncomingTargetExpansion.right hc hab hOne profile.large.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) := by
    rw [hSmall]
    exact hSideNe.symm
  have hChange := targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
    profile.large.1 hNe
  have hActiveMerged : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {smallEndpoint data hc hab hOne star input profile,
        largeEndpoint data hc hab hOne star input profile} := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
    exact hActive
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hInternal]
    exact Finset.mem_singleton_self internal
  obtain ⟨hInternalClass, hRamClass⟩ := sheet_classes_of_active_pair data fullDim hc hab hOne
    (selectedBlock data hc hab hOne star input) internal
    (smallEndpoint data hc hab hOne star input profile)
    (largeEndpoint data hc hab hOne star input profile)
    hActiveMerged hInternalMem hSmallInc hLargeInc hLargeNd hChange
  have hFlag := endpoint_block_eq_flag_local data fullDim hc hab hOne hCompat.1
    (selectedBlock data hc hab hOne star input)
    ⟨profile.large.1, profile.large_survives⟩
    (by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.large.2)
    hLargeNd hChange
  exact ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, hInternalClass, hFlag, hRamClass⟩

/-- **Figure 31, `M^{(2)}`-orientation.**  The mirror of
`selected_sheet_classes_of_small`: the divalent original endpoint is restored to
the *larger* survivor, so the smaller survivor's canonical endpoint is the
unramified one. -/
theorem selected_sheet_classes_of_large
    (hLarge : divalentOccurrence data hc hab hOne fullDim star = largeTarget input profile) :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {smallEndpoint data hc hab hOne star input profile,
          largeEndpoint data hc hab hOne star input profile} ∧
      Incident data internal (smallEndpoint data hc hab hOne star input profile) ∧
      Incident data internal (largeEndpoint data hc hab hOne star input profile) ∧
      (data.edgePartition internal.1.1).block internal.1.2 =
        (data.vertexPartition
            (smallEndpoint data hc hab hOne star input profile).1.1).block
          (smallEndpoint data hc hab hOne star input profile).1.2 ∧
      (data.vertexPartition
            (smallEndpoint data hc hab hOne star input profile).1.1).block
          (smallEndpoint data hc hab hOne star input profile).1.2 =
        ((contractDatum data hc hab hOne).edgePartition
            (smallTarget input profile)).block profile.small.1.1.2 ∧
      (data.vertexPartition
            (largeEndpoint data hc hab hOne star input profile).1.1).block
          (largeEndpoint data hc hab hOne star input profile).1.2 =
        (mergedPartition data a b).block (selectedBlock data hc hab hOne star input).1 := by
  classical
  obtain ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, hSmallNd, _⟩ :=
    selected_fibre_census data hc hab hOne fullDim hForest hCompat star input profile
  have hSideNe := small_large_side_ne data hc hab hOne fullDim star input profile (Or.inr hLarge)
  have hNe : IncomingTargetExpansion.right hc hab hOne profile.small.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) := by
    rw [hLarge]
    exact hSideNe
  have hChange := targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
    profile.small.1 hNe
  have hActiveMerged : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {largeEndpoint data hc hab hOne star input profile,
        smallEndpoint data hc hab hOne star input profile} := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hActive]
    exact Finset.pair_comm _ _
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hInternal]
    exact Finset.mem_singleton_self internal
  obtain ⟨hInternalClass, hRamClass⟩ := sheet_classes_of_active_pair data fullDim hc hab hOne
    (selectedBlock data hc hab hOne star input) internal
    (largeEndpoint data hc hab hOne star input profile)
    (smallEndpoint data hc hab hOne star input profile)
    hActiveMerged hInternalMem hLargeInc hSmallInc hSmallNd hChange
  have hFlag := endpoint_block_eq_flag_local data fullDim hc hab hOne hCompat.1
    (selectedBlock data hc hab hOne star input)
    ⟨profile.small.1, profile.small_survives⟩
    (by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.small.2)
    hSmallNd hChange
  exact ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, hInternalClass, hFlag, hRamClass⟩

/-- **Figure 31's selected endpoint and internal sheet classes, unconditional.**

Both orientations at once: the selected pruned fibre is one internal occurrence
joining the two named survivors' canonical endpoints, one of which is
unramified; the internal occurrence, that endpoint and its own retained wall
flag all carry one and the same literal sheet set, and the other endpoint
carries the entire merged wall class `A_0`.

The hypotheses are those of
`W3Nd2IncomingSelectedCensus.selected_fibre_census`, and are jointly satisfiable
for the same reason: an actual full-dimensional incoming presentation whose
contraction of the single edge `contracted` between `a` and `b` is a forest with
dangling compatibility, a genuine trivalent star at the contracted wall, a W3
source input for it, and a Figure 31 nd2 profile of its distinguished block.
Nothing here forces the fibre to be empty or the two survivors to coincide, and
the ramified/unramified split is a real dichotomy rather than a vacuous one: the
two branches are the paper's `M^{(1)}` and `M^{(2)}`.

This identifies the *classes*; matching them against the stored representatives
of the Figure 31 candidates through `PartitionNormalization`, and the r0
background blocks, are separate obligations and are not proved here. -/
theorem selected_sheet_classes :
    ∃ internal : data.SourceEdge, ∃ ramified unramified : data.SourceVertex,
      ∃ flag : (contractDatum data hc hab hOne).SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) = {ramified, unramified} ∧
      ({ramified, unramified} : Finset data.SourceVertex) =
        {smallEndpoint data hc hab hOne star input profile,
          largeEndpoint data hc hab hOne star input profile} ∧
      (flag = profile.small.1 ∨ flag = profile.large.1) ∧
      endpoint data hc hab hOne flag = unramified ∧
      Incident data internal ramified ∧
      Incident data internal unramified ∧
      (data.edgePartition internal.1.1).block internal.1.2 =
        (data.vertexPartition unramified.1.1).block unramified.1.2 ∧
      (data.vertexPartition unramified.1.1).block unramified.1.2 =
        ((contractDatum data hc hab hOne).edgePartition flag.1.1).block flag.1.2 ∧
      (data.vertexPartition ramified.1.1).block ramified.1.2 =
        (mergedPartition data a b).block (selectedBlock data hc hab hOne star input).1 := by
  classical
  rcases divalentOccurrence_eq_small_or_large data hc hab hOne fullDim hForest hCompat
    star input profile with hSmall | hLarge
  · obtain ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, hInternalClass, hFlag,
      hRamClass⟩ :=
      selected_sheet_classes_of_small data hc hab hOne fullDim hForest hCompat star input
        profile hSmall
    exact ⟨internal, smallEndpoint data hc hab hOne star input profile,
      largeEndpoint data hc hab hOne star input profile, profile.large.1,
      hInternal, hActive, rfl, Or.inr rfl, rfl, hSmallInc, hLargeInc, hInternalClass,
      hFlag, hRamClass⟩
  · obtain ⟨internal, hInternal, hActive, hSmallInc, hLargeInc, hInternalClass, hFlag,
      hRamClass⟩ :=
      selected_sheet_classes_of_large data hc hab hOne fullDim hForest hCompat star input
        profile hLarge
    exact ⟨internal, largeEndpoint data hc hab hOne star input profile,
      smallEndpoint data hc hab hOne star input profile, profile.small.1,
      hInternal, hActive.trans (Finset.pair_comm _ _), Finset.pair_comm _ _, Or.inl rfl, rfl,
      hLargeInc, hSmallInc, hInternalClass, hFlag, hRamClass⟩

end Selected

end DraismaVargas.LocalCases.W3Nd2IncomingSheetClasses
