import DraismaVargas.LocalCases.W3Nd2IncomingSheetClasses
import DraismaVargas.LocalCases.W3Nd3SourceCandidates
import DraismaVargas.LocalCases.W4IncomingCensus
import DraismaVargas.LocalCases.W3Nd2IncomingBackground

/-!
# The selected incoming fibre and its sheet classes in the W3 nd3-t3 case

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4), with Positions I/II.a/II.b of case `{w3-r1-nd3-t2}`.  This file
follows the labelling of Figure 30 for the two choices `α = 3` and `α = 4`
(the prose of the case assigns the two members to them the other way round),
and reads the individual regrown columns off the figure.

This is the nd3 analogue of `W3Nd2IncomingSelectedCensus` together with
`W3Nd2IncomingSheetClasses`, for an **arbitrary** incoming W3 nd3 datum: a
full-dimensional presentation whose contraction of a single edge `contracted`
between `a` and `b` is a forest with dangling compatibility, a trivalent star
at the contracted wall, a `W3SourceInput` for it, an `Nd3Profile` of its
distinguished block, and the doubled direction `hSame`.  No further hypothesis
is added.

## Three places where nd3 genuinely differs from nd2

* **There is no residual sheet.**  `k₂ + k₃ = |A₀|` makes the doubled
  direction cover `A₀` exactly, so both smaller survivors are live and
  `W3Nd2Survival.exists_residualSheet` has no analogue.  Concretely
  `selected_fibre_census_of_largest` finds **two** surviving internal
  occurrences, not one survivor and one dangler.
* **The divalent endpoint is a branch vertex.**  In both Figure 30 members the
  canonical endpoint over the divalent original endpoint has non-dangling
  valency **three**, not two.  So `PrunedDivalentFibre.internalEdges_card_le_one`,
  which needs a divalent wall, does not apply and is not used; the fibre census
  is obtained instead from the pruned-tree valency formula
  `PrunedFibreTree.nonDanglingValency_mergedVertex_eq_sum` together with the
  unramified side's no-return.
* **The fibre is not a single occurrence.**  In `M⁽²⁾` (`α = 4`) it is a path of
  two occurrences with three active constituents.  Every statement below is
  therefore an identity of literal **occurrence** sets.

## The two orientations

`W3Nd2IncomingDirection.exists_ramified_block_at_divalent` and
`W3Nd2IncomingDirection.exists_survivor_over_direction` are profile-free and are
reused verbatim: the unique retained wall direction at the divalent original
endpoint carries a survivor of the distinguished block, hence is one of the two
actual surviving directions `t₃` (doubled) and `t₄` (largest).  That is
`divalentOccurrence_eq_shared_or_largest`, and the two alternatives are exactly
Figure 30's `M⁽¹⁾` and `M⁽²⁾`.

* `M⁽¹⁾`, `divalentOccurrence = t₃`: the two smaller survivors are restored to
  the divalent endpoint and share **one** canonical endpoint, which is the
  branch vertex; the largest survivor's endpoint is the unramified one; the
  fibre is one internal occurrence.
* `M⁽²⁾`, `divalentOccurrence = t₄`: the largest survivor is restored to the
  divalent endpoint and its canonical endpoint is the branch vertex; the two
  smaller survivors have **distinct** unramified canonical endpoints; the fibre
  is two internal occurrences.

In both members the unramified endpoints are Case (r0-nd2) and fix the internal
occurrences' sheet classes, while refinement across them collapses the
non-dangling union onto the branch vertex: `A₀` is literally the branch
vertex's sheet class.

## Main results

* `divalentOccurrence_eq_shared_or_largest` -- the `M⁽¹⁾`/`M⁽²⁾` dichotomy;
* `selected_fibre_census_of_shared`, `selected_fibre_census_of_largest` -- the
  exact occurrence and constituent census of the selected pruned fibre in each
  orientation, with the non-dangling valencies;
* `selected_sheet_classes_of_shared`, `selected_sheet_classes_of_largest` and
  the unconditional `selected_sheet_classes` -- those censuses together with
  the literal sheet-set identities they determine;
* `background_dichotomy` -- Case `{w3-r0}` at every other wall block, which is
  `W3Nd2IncomingBackground`'s statement applied verbatim, that module being
  profile-free.

Matching these classes against the stored representatives of the Figure 30
candidates through `PartitionNormalization`, and the original-coordinate
restatement, are `W3Nd3IncomingMatching` and `W3Nd3ArbitraryExit`.
-/

namespace DraismaVargas.LocalCases.W3Nd3IncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion IncomingW2TargetPlacement TargetExpansion
open PrunedFibreValency PrunedFibreTree
open FullContractionFibre
open W4IncomingRetainedFlags
open W3Nd2IncomingTargetPlacement W3Nd2IncomingDirection
open W3Nd2IncomingSelectedCensus W3Nd2IncomingSheetClasses

variable {target : CFGraph} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## The three canonical endpoints of the Figure 30 profile -/

/-- The canonical same-sheet endpoint of the first smaller survivor `e₂`. -/
noncomputable abbrev firstEndpoint
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd3Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) : data.SourceVertex :=
  endpoint data hc hab hOne profile.first.1

/-- The canonical same-sheet endpoint of the second smaller survivor `e₃`. -/
noncomputable abbrev secondEndpoint
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd3Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) : data.SourceVertex :=
  endpoint data hc hab hOne profile.second.1

/-- The canonical same-sheet endpoint of the largest survivor `e₄`. -/
noncomputable abbrev largestEndpoint
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd3Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock) : data.SourceVertex :=
  endpoint data hc hab hOne profile.largest.1

/-- The distinguished wall block of an nd3 profile has non-dangling valency
three: its three literal survivors are pairwise distinct. -/
theorem profile_valency {wall : target.V} {data : GluingDatum target degree}
    {block : WallBlock data wall} (profile : Nd3Profile data block) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 := by
  classical
  rw [← card_survivors, profile.surviving,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h ↦ h.elim profile.first_ne_second profile.first_ne_largest),
    Finset.card_pair profile.second_ne_largest]

/-! ## Which star direction sits at the divalent original endpoint -/

/-- **The isolated direction carries a survivor of the distinguished block.**
This is the profile-free half of
`W3Nd2IncomingDirection.divalentOccurrence_eq_small_or_large`: forest
additivity puts the contracted unit of ramification on an old block over the
divalent original endpoint, local no-return there produces a survivor in every
direction of that endpoint, and the inherited dangling compatibility carries it
down to the contracted distinguished block. -/
theorem exists_survivor_over_divalentOccurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star) :
    ∃ edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (selectedVertex data hc hab hOne star input),
      ¬ IsDangling (contractDatum data hc hab hOne) edge.1 ∧
        edge.1.1.1 = divalentOccurrence data hc hab hOne fullDim star := by
  classical
  let isolated := divalentOccurrence data hc hab hOne fullDim star
  have hIsolated := divalentOccurrence_spec data hc hab hOne fullDim star
  have hEndpointSum := (endpoints_of_threeStar data hc hab hOne fullDim.valid
    fullDim.changeMinimal star).1
  rcases exists_ramified_block_at_divalent data hc hab hOne fullDim hForest
    star input with hLeft | hRight
  · obtain ⟨block, hBlock, hRamification⟩ := hLeft.2
    have hSide : IncomingTargetExpansion.right hc hab hOne isolated = false := by
      rcases hIsolated.2 with hAtLeft | hAtRight
      · simpa only [isolated] using hAtLeft.2
      · omega
    have hAt : unfoldEdge hc hab hOne isolated ∈ GluingDatum.incidentEdges a :=
      (right_eq_false_iff_of_incident hc hab hOne isolated hIsolated.1).mp hSide
    obtain ⟨oldEdge, hSurvives, hTarget⟩ :=
      exists_survivor_over_direction data fullDim.danglingEdgeNoGlue
        fullDim.connected block hRamification hLeft.1
        (unfoldEdge hc hab hOne isolated) hAt
    have hAway : oldEdge.1.1.1 ≠ contracted := by
      intro hEq
      exact unfoldEdge_ne_contracted hc hab hOne isolated (hTarget.symm.trans hEq)
    let oldAway : {edge : data.SourceEdge // edge.1.1 ≠ contracted} := ⟨oldEdge.1, hAway⟩
    let oldTargetAway : {edge : target.edges // edge ≠ contracted} := ⟨oldEdge.1.1.1, hAway⟩
    let mapped := sourceEdgeMap data hc hab hOne oldAway
    have hMappedTarget : mapped.1.1 = isolated := by
      have hTargetAway : oldTargetAway =
          ⟨unfoldEdge hc hab hOne isolated,
            unfoldEdge_ne_contracted hc hab hOne isolated⟩ := Subtype.ext hTarget
      change foldEdge hc hab hOne oldTargetAway = isolated
      rw [hTargetAway, foldEdge_unfoldEdge]
    have hMappedSurvives : ¬ IsDangling (contractDatum data hc hab hOne) mapped := by
      intro hDangling
      exact hSurvives (hCompat.2 oldAway hDangling)
    have hMappedIncident := incident_sourceEdgeMap data hc hab hOne oldAway oldEdge.2
    rw [sourceVertexMap_left_eq_wallBlock data hc hab hOne
      input.distinguishedBlock block hBlock] at hMappedIncident
    exact ⟨⟨mapped, hMappedIncident⟩, hMappedSurvives, hMappedTarget⟩
  · obtain ⟨block, hBlock, hRamification⟩ := hRight.2
    have hSide : IncomingTargetExpansion.right hc hab hOne isolated = true := by
      rcases hIsolated.2 with hAtLeft | hAtRight
      · omega
      · simpa only [isolated] using hAtRight.2
    have hAt : unfoldEdge hc hab hOne isolated ∈ GluingDatum.incidentEdges b :=
      (right_eq_true_iff hc hab hOne isolated).mp hSide
    obtain ⟨oldEdge, hSurvives, hTarget⟩ :=
      exists_survivor_over_direction data fullDim.danglingEdgeNoGlue
        fullDim.connected block hRamification hRight.1
        (unfoldEdge hc hab hOne isolated) hAt
    have hAway : oldEdge.1.1.1 ≠ contracted := by
      intro hEq
      exact unfoldEdge_ne_contracted hc hab hOne isolated (hTarget.symm.trans hEq)
    let oldAway : {edge : data.SourceEdge // edge.1.1 ≠ contracted} := ⟨oldEdge.1, hAway⟩
    let oldTargetAway : {edge : target.edges // edge ≠ contracted} := ⟨oldEdge.1.1.1, hAway⟩
    let mapped := sourceEdgeMap data hc hab hOne oldAway
    have hMappedTarget : mapped.1.1 = isolated := by
      have hTargetAway : oldTargetAway =
          ⟨unfoldEdge hc hab hOne isolated,
            unfoldEdge_ne_contracted hc hab hOne isolated⟩ := Subtype.ext hTarget
      change foldEdge hc hab hOne oldTargetAway = isolated
      rw [hTargetAway, foldEdge_unfoldEdge]
    have hMappedSurvives : ¬ IsDangling (contractDatum data hc hab hOne) mapped := by
      intro hDangling
      exact hSurvives (hCompat.2 oldAway hDangling)
    have hMappedIncident := incident_sourceEdgeMap data hc hab hOne oldAway oldEdge.2
    rw [sourceVertexMap_right_eq_wallBlock data hc hab hOne
      input.distinguishedBlock block hBlock] at hMappedIncident
    exact ⟨⟨mapped, hMappedIncident⟩, hMappedSurvives, hMappedTarget⟩

/-- **Figure 30's two orientations.**  The unique retained wall direction at the
divalent original endpoint is either the doubled direction `t₃` shared by the
two smaller survivors, or the largest survivor's direction `t₄`.  These are
`M⁽¹⁾` (`α = 3`) and `M⁽²⁾` (`α = 4`).  The residual third direction `t₂` of the
star is excluded, exactly as in nd2. -/
theorem divalentOccurrence_eq_shared_or_largest
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd3Profile (contractDatum data hc hab hOne)
      input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1 ∨
      divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1 := by
  classical
  obtain ⟨mapped, hSurvives, hTarget⟩ := exists_survivor_over_divalentOccurrence
    data hc hab hOne fullDim hForest hCompat star input
  have hMember : mapped ∈ survivors (contractDatum data hc hab hOne)
      input.distinguishedBlock :=
    (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock mapped).mpr
      hSurvives
  rw [profile.surviving] at hMember
  rcases Finset.mem_insert.mp hMember with hFirst | hRest
  · exact Or.inl (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (selectedVertex data hc hab hOne star input) ↦ edge.1.1.1) hFirst))
  · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
    · refine Or.inl ((hTarget.symm.trans (congrArg
        (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
          (selectedVertex data hc hab hOne star input) ↦ edge.1.1.1) hSecond)).trans
          hSame.symm)
    · exact Or.inr (hTarget.symm.trans (congrArg
        (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
          (selectedVertex data hc hab hOne star input) ↦ edge.1.1.1)
        (Finset.mem_singleton.mp hLargest)))


/-! ## Pruned-fibre counting at a trivalent wall

`PrunedDivalentFibre.internalEdges_card_le_one` needs a divalent wall and is
therefore unavailable here.  What replaces it is the pruned-tree valency
formula together with no-return on the **unramified** original endpoint only. -/

/-- The two literal ends of an internal occurrence lie above the two original
endpoints of the contracted occurrence.  Local copy of
`W4IncomingPrunedFibre.internalEdge_endpoints`, which is stated for a four-star
wall datum. -/
theorem internalEdge_endpoints_local
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (edge : data.SourceEdge)
    (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    (data.sourceEnds edge).1.1.1 = a ∧ (data.sourceEnds edge).2.1.1 = b := by
  obtain ⟨_, hTarget, _⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp hEdge
  constructor
  · change (edge.1.1 : target.V × target.V).1 = a
    rw [hTarget, hc]
  · change (edge.1.1 : target.V × target.V).2 = b
    rw [hTarget, hc]

open Classical in
/-- The end of an occurrence over the contracted target edge that lies above a
prescribed original endpoint. -/
noncomputable def sideEnd (data : GluingDatum target degree) (side : target.V)
    (edge : data.SourceEdge) : data.SourceVertex :=
  if (data.sourceEnds edge).1.1.1 = side then (data.sourceEnds edge).1
  else (data.sourceEnds edge).2

open Classical in
/-- Its opposite end. -/
noncomputable def otherEnd (data : GluingDatum target degree) (side : target.V)
    (edge : data.SourceEdge) : data.SourceVertex :=
  if (data.sourceEnds edge).1.1.1 = side then (data.sourceEnds edge).2
  else (data.sourceEnds edge).1

theorem sideEnd_incident (data : GluingDatum target degree) (side : target.V)
    (edge : data.SourceEdge) : Incident data edge (sideEnd data side edge) := by
  classical
  rw [sideEnd]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem otherEnd_incident (data : GluingDatum target degree) (side : target.V)
    (edge : data.SourceEdge) : Incident data edge (otherEnd data side edge) := by
  classical
  rw [otherEnd]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

section Ends

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (vertex : (contractDatum data hc hab hOne).SourceVertex)
  (side : target.V) (hSide : side = a ∨ side = b)
  (edge : data.SourceEdge)
  (hEdge : edge ∈ internalEdges data hc hab hOne vertex)

include hab hEdge hSide

theorem sideEnd_target : (sideEnd data side edge).1.1 = side := by
  classical
  obtain ⟨hLeft, hRight⟩ := internalEdge_endpoints_local data hc hab hOne vertex edge hEdge
  rcases hSide with hA | hB
  · have hCond : (data.sourceEnds edge).1.1.1 = side := hLeft.trans hA.symm
    rw [sideEnd, if_pos hCond]
    exact hCond
  · have hCond : ¬ (data.sourceEnds edge).1.1.1 = side := by
      rw [hLeft, hB]
      exact hab
    rw [sideEnd, if_neg hCond]
    exact hRight.trans hB.symm

theorem otherEnd_target_ne : (otherEnd data side edge).1.1 ≠ side := by
  classical
  obtain ⟨hLeft, hRight⟩ := internalEdge_endpoints_local data hc hab hOne vertex edge hEdge
  rcases hSide with hA | hB
  · have hCond : (data.sourceEnds edge).1.1.1 = side := hLeft.trans hA.symm
    rw [otherEnd, if_pos hCond, hRight, hA]
    exact Ne.symm hab
  · have hCond : ¬ (data.sourceEnds edge).1.1.1 = side := by
      rw [hLeft, hB]
      exact hab
    rw [otherEnd, if_neg hCond, hLeft, hB]
    exact hab

omit hSide in
theorem sideEnd_mem_active :
    sideEnd data side edge ∈ activeFibreVertices data hc hab hOne vertex := by
  classical
  have hEnds := (sourceEnds_mem_activeFibre_iff data hc hab hOne vertex edge).mpr hEdge
  rw [sideEnd]
  split
  · exact hEnds.1
  · exact hEnds.2

omit hSide in
theorem otherEnd_mem_active :
    otherEnd data side edge ∈ activeFibreVertices data hc hab hOne vertex := by
  classical
  have hEnds := (sourceEnds_mem_activeFibre_iff data hc hab hOne vertex edge).mpr hEdge
  rw [otherEnd]
  split
  · exact hEnds.2
  · exact hEnds.1

end Ends

/-- No-return on the unramified side: a source vertex of vanishing target
change carries at most one survivor per target direction, whether it is
divalent or trivalent.  The nd2 half is
`DivalentSourceLocal.sourceEdge_eq_of_same_target`, the nd3 half is
`W4IncomingCensus.sourceEdge_eq_of_same_target_of_nd3_r0`; neither needs a
four-valent wall. -/
theorem sourceEdge_eq_of_same_target_unramified
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (point : data.SourceVertex)
    (hChange : data.targetChange point.1.1 = 0)
    (hNd : nonDanglingValency data point = 2 ∨ nonDanglingValency data point = 3)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point)
    (hTarget : first.1.1 = second.1.1) : first = second := by
  have hR : data.localRamification point.1.1 ⟨point.1.2, point.2⟩ = 0 :=
    localRamification_eq_zero_of_targetChange_eq_zero data fullDim.valid point.1.1
      hChange _
  rcases hNd with hTwo | hThree
  · exact DivalentSourceLocal.sourceEdge_eq_of_same_target data
      fullDim.danglingEdgeNoGlue point hTwo (by omega) first second hFirst hSecond
      hFirstInc hSecondInc hTarget
  · exact W4IncomingCensus.sourceEdge_eq_of_same_target_of_nd3_r0 data
      fullDim.danglingEdgeNoGlue point hThree hR first second hFirst hSecond
      hFirstInc hSecondInc hTarget

section Counting

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (block : (mergedPartition data a b).Blocks)
  (hWallNd : nonDanglingValency (contractDatum data hc hab hOne)
    (mergedVertex data hc hab hOne block) = 3)

include hCompat hWallNd

theorem activeFibre_nonempty :
    (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty :=
  activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne hCompat _
    (by rw [hWallNd]; omega)

include hForest

/-- **`lemma-ndval-of-GqA0` at an nd3 wall.**  The pruned valency excesses of
the selected fibre sum to exactly one. -/
theorem active_excess_sum :
    (∑ point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block),
      ((nonDanglingValency data point : ℤ) - 2)) = 1 := by
  have hFormula := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat
    hForest block (by rw [hWallNd]; omega)
  rw [hWallNd] at hFormula
  omega

omit hForest hCompat hWallNd

include fullDim in
theorem active_excess_nonneg (point : data.SourceVertex)
    (hPoint : point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)) :
    0 ≤ (nonDanglingValency data point : ℤ) - 2 := by
  have hNe := ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).2
  have hNeOne := nonDanglingValency_ne_one data fullDim.connected point
  omega

include fullDim hForest hCompat hWallNd

/-- Every active constituent of the selected nd3 fibre is divalent or
trivalent. -/
theorem active_valency_two_or_three (point : data.SourceVertex)
    (hPoint : point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)) :
    nonDanglingValency data point = 2 ∨ nonDanglingValency data point = 3 := by
  have hSum := active_excess_sum data hc hab hOne hForest hCompat block hWallNd
  have hLe := Finset.single_le_sum
    (f := fun point : data.SourceVertex ↦ ((nonDanglingValency data point : ℤ) - 2))
    (fun point hPoint ↦ active_excess_nonneg data hc hab hOne fullDim block point hPoint)
    hPoint
  rw [hSum] at hLe
  have hNe := ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).2
  have hNeOne := nonDanglingValency_ne_one data fullDim.connected point
  omega

/-- **There is at most one branch vertex in the selected fibre.** -/
theorem active_valency_three_unique (first second : data.SourceVertex)
    (hFirst : first ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hSecond : second ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hNe : first ≠ second)
    (hFirstNd : nonDanglingValency data first = 3) :
    nonDanglingValency data second ≠ 3 := by
  classical
  intro hSecondNd
  have hSum := active_excess_sum data hc hab hOne hForest hCompat block hWallNd
  have hSubset : ({first, second} : Finset data.SourceVertex) ⊆
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) := by
    intro point hPoint
    rcases Finset.mem_insert.mp hPoint with rfl | hPoint
    · exact hFirst
    · exact (Finset.mem_singleton.mp hPoint) ▸ hSecond
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg (f := fun point : data.SourceVertex ↦
      ((nonDanglingValency data point : ℤ) - 2)) hSubset
    (fun point hPoint _ ↦ active_excess_nonneg data hc hab hOne fullDim block point hPoint)
  rw [Finset.sum_pair hNe, hSum, hFirstNd, hSecondNd] at hLe
  omega

/-- **The unramified side bounds the internal occurrence count.**  Each active
constituent above the endpoint of vanishing target change carries at most one
occurrence over the contracted direction, so sending an internal occurrence to
that end is injective. -/
theorem sideEnd_injOn
    (side : target.V) (hSide : side = a ∨ side = b)
    (hChange : data.targetChange side = 0) :
    Set.InjOn (sideEnd data side)
      ↑(internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)) := by
  classical
  intro first hFirst second hSecond hEq
  have hFirstMem : first ∈ internalEdges data hc hab hOne
    (mergedVertex data hc hab hOne block) := Finset.mem_coe.mp hFirst
  have hSecondMem : second ∈ internalEdges data hc hab hOne
    (mergedVertex data hc hab hOne block) := Finset.mem_coe.mp hSecond
  obtain ⟨hFirstSurvives, hFirstTarget, _⟩ :=
    (mem_internalEdges data hc hab hOne _ first).mp hFirstMem
  obtain ⟨hSecondSurvives, hSecondTarget, _⟩ :=
    (mem_internalEdges data hc hab hOne _ second).mp hSecondMem
  have hPointTarget : (sideEnd data side first).1.1 = side :=
    sideEnd_target data hc hab hOne _ side hSide first hFirstMem
  have hPointActive := sideEnd_mem_active data hc hab hOne _ side first hFirstMem
  refine sourceEdge_eq_of_same_target_unramified data fullDim (sideEnd data side first)
    (by rw [hPointTarget]; exact hChange)
    (active_valency_two_or_three data hc hab hOne fullDim hForest hCompat block hWallNd
      _ hPointActive)
    first second hFirstSurvives hSecondSurvives
    (sideEnd_incident data side first) ?_
    (hFirstTarget.trans hSecondTarget.symm)
  have hInc := sideEnd_incident data side second
  rwa [← hEq] at hInc

/-- Sending an internal occurrence to its end above the unramified original
endpoint is injective, so it bounds the internal occurrence count. -/
theorem internalEdges_card_le_side_card
    (side : target.V) (hSide : side = a ∨ side = b)
    (hChange : data.targetChange side = 0) :
    (internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card ≤
      ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
        fun point ↦ point.1.1 = side).card := by
  classical
  refine Finset.card_le_card_of_injOn (sideEnd data side) ?_
    (sideEnd_injOn data hc hab hOne fullDim hForest hCompat block hWallNd side hSide hChange)
  intro edge hEdge
  exact Finset.mem_filter.mpr
    ⟨sideEnd_mem_active data hc hab hOne _ side edge hEdge,
      sideEnd_target data hc hab hOne _ side hSide edge hEdge⟩

/-- The internal occurrences of the selected fibre are in bijection with the
active constituents above the unramified endpoint that they meet. -/
theorem sideEnd_image
    (side : target.V) (hSide : side = a ∨ side = b)
    (hChange : data.targetChange side = 0)
    (hCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        fun point ↦ point.1.1 = side).card ≤
      (internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card) :
    (internalEdges data hc hab hOne
        (mergedVertex data hc hab hOne block)).image (sideEnd data side) =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
        fun point ↦ point.1.1 = side := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro point hPoint
    obtain ⟨edge, hEdge, hImage⟩ := Finset.mem_image.mp hPoint
    exact hImage ▸ Finset.mem_filter.mpr
      ⟨sideEnd_mem_active data hc hab hOne _ side edge hEdge,
        sideEnd_target data hc hab hOne _ side hSide edge hEdge⟩
  · rw [Finset.card_image_of_injOn
      (sideEnd_injOn data hc hab hOne fullDim hForest hCompat block hWallNd side hSide
        hChange)]
    exact hCard

/-- Consequently the **ramified** side of the selected fibre has at most one
active constituent: the branch vertex of Figure 30. -/
theorem otherSide_card_le_one
    (side : target.V) (hSide : side = a ∨ side = b)
    (hChange : data.targetChange side = 0) :
    ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
      fun point ↦ ¬ point.1.1 = side).card ≤ 1 := by
  classical
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
    hForest block (activeFibre_nonempty data hc hab hOne hCompat block hWallNd)
  have hSplit : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
      fun point ↦ point.1.1 = side).card +
      ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
      fun point ↦ ¬ point.1.1 = side).card =
      (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).card :=
    Finset.card_filter_add_card_filter_not _
  have hBound := internalEdges_card_le_side_card data hc hab hOne fullDim hForest hCompat
    block hWallNd side hSide hChange
  omega

end Counting


/-! ## Bookkeeping for the three survivors -/

theorem profile_first_survives {wall : target.V} {data : GluingDatum target degree}
    {block : WallBlock data wall} (profile : Nd3Profile data block) :
    ¬ IsDangling data profile.first.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_self _ _

theorem profile_second_survives {wall : target.V} {data : GluingDatum target degree}
    {block : WallBlock data wall} (profile : Nd3Profile data block) :
    ¬ IsDangling data profile.second.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem profile_largest_survives {wall : target.V} {data : GluingDatum target degree}
    {block : WallBlock data wall} (profile : Nd3Profile data block) :
    ¬ IsDangling data profile.largest.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- A canonical same-sheet endpoint lies above one of the two original
endpoints of the contracted occurrence. -/
theorem endpoint_target_mem
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (endpoint data hc hab hOne edge).1.1 = a ∨
      (endpoint data hc hab hOne edge).1.1 = b := by
  rw [endpoint_target]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every wall direction other than the isolated one is restored to the
opposite original endpoint.  This is uniqueness of the divalent-side
occurrence, read as a statement about the actual side predicate. -/
theorem side_ne_of_ne_divalentOccurrence
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (edge : (contract target hab hOne).edges)
    (hAt : edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩)
    (hNe : edge ≠ divalentOccurrence data hc hab hOne fullDim star) :
    IncomingTargetExpansion.right hc hab hOne edge ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) := by
  intro hEq
  refine hNe (divalentOccurrence_unique data hc hab hOne fullDim star edge ⟨hAt, ?_⟩)
  rcases (divalentOccurrence_spec data hc hab hOne fullDim star).2 with hLeft | hRight
  · exact Or.inl ⟨hLeft.1, hEq.trans hLeft.2⟩
  · exact Or.inr ⟨hRight.1, hEq.trans hRight.2⟩

/-! ## The branch vertex bounds the number of internal occurrences -/

/-- Internal occurrences all meet the unique active constituent above the
ramified original endpoint. -/
theorem internal_incident_otherEnd
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (side : target.V) (hSide : side = a ∨ side = b) (point : data.SourceVertex)
    (hFilter : (activeFibreVertices data hc hab hOne vertex).filter
      (fun other ↦ ¬ other.1.1 = side) = {point})
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    Incident data edge point := by
  classical
  have hMem : otherEnd data side edge ∈
      (activeFibreVertices data hc hab hOne vertex).filter
        (fun other ↦ ¬ other.1.1 = side) :=
    Finset.mem_filter.mpr ⟨otherEnd_mem_active data hc hab hOne vertex side edge hEdge,
      otherEnd_target_ne data hc hab hOne vertex side hSide edge hEdge⟩
  rw [hFilter, Finset.mem_singleton] at hMem
  exact hMem ▸ otherEnd_incident data side edge

/-- Internal occurrences all meet the unique active constituent above the
unramified original endpoint, when there is only one. -/
theorem internal_incident_sideEnd
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (side : target.V) (hSide : side = a ∨ side = b) (point : data.SourceVertex)
    (hFilter : (activeFibreVertices data hc hab hOne vertex).filter
      (fun other ↦ other.1.1 = side) = {point})
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    Incident data edge point := by
  classical
  have hMem : sideEnd data side edge ∈
      (activeFibreVertices data hc hab hOne vertex).filter
        (fun other ↦ other.1.1 = side) :=
    Finset.mem_filter.mpr ⟨sideEnd_mem_active data hc hab hOne vertex side edge hEdge,
      sideEnd_target data hc hab hOne vertex side hSide edge hEdge⟩
  rw [hFilter, Finset.mem_singleton] at hMem
  exact hMem ▸ sideEnd_incident data side edge

/-- **Occurrence count at the branch vertex.**  Retained wall occurrences and
internal occurrences at one active constituent are disjoint families of
survivors there, so their total is bounded by its non-dangling valency. -/
theorem extra_add_internal_card_le
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (point : data.SourceVertex)
    (hInternal : ∀ edge ∈ internalEdges data hc hab hOne vertex,
      Incident data edge point)
    (extra : Finset data.SourceEdge)
    (hExtra : ∀ edge ∈ extra, (¬ IsDangling data edge) ∧ Incident data edge point ∧
      edge.1.1 ≠ contracted) :
    extra.card + (internalEdges data hc hab hOne vertex).card ≤
      nonDanglingValency data point := by
  classical
  have hDisjoint : Disjoint extra (internalEdges data hc hab hOne vertex) := by
    rw [Finset.disjoint_left]
    intro edge hFirst hSecond
    exact (hExtra edge hFirst).2.2
      ((mem_internalEdges data hc hab hOne vertex edge).mp hSecond).2.1
  have hSubset : extra ∪ internalEdges data hc hab hOne vertex ⊆
      nonDanglingIncident data point := by
    intro edge hEdge
    rcases Finset.mem_union.mp hEdge with hFirst | hSecond
    · exact (mem_nonDanglingIncident data point edge).mpr
        ⟨(hExtra edge hFirst).1, (hExtra edge hFirst).2.1⟩
    · exact (mem_nonDanglingIncident data point edge).mpr
        ⟨((mem_internalEdges data hc hab hOne vertex edge).mp hSecond).1,
          hInternal edge hSecond⟩
  have hCard := Finset.card_le_card hSubset
  rwa [Finset.card_union_of_disjoint hDisjoint, card_nonDanglingIncident] at hCard


/-- The retained incoming copy of a wall occurrence lies over the unfolded
target occurrence. -/
theorem embedding_target
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (sourceEdgeEmbedding data hc hab hOne edge).1.1 =
      unfoldEdge hc hab hOne edge.1.1 :=
  congrArg Prod.fst (IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne edge)

/-! ## The selected fibre of an arbitrary incoming nd3 datum -/

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
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include fullDim hForest hCompat

/-- **Figure 30's `M⁽¹⁾` orientation (`α = 3`), exact fibre census.**

If the unique retained wall direction at the divalent original endpoint is the
**doubled** direction `t₃`, then the two smaller survivors `e₂`, `e₃` are
restored to that endpoint and share a single canonical same-sheet endpoint,
which is trivalent — the branch vertex of `M⁽¹⁾`.  The largest survivor `e₄`
is restored to the other endpoint, its canonical endpoint is divalent, and the
selected pruned fibre is exactly one surviving occurrence joining the two.

The hypotheses are the incoming bundle already shown jointly satisfiable in the
nd2 case, with `Nd2Profile` replaced by `Nd3Profile` and the doubled direction
`hSame` added; `hShared` is one of the two alternatives of
`divalentOccurrence_eq_shared_or_largest`, both of which genuinely occur. -/
theorem selected_fibre_census_of_shared
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star =
      profile.first.1.1.1) :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {firstEndpoint data hc hab hOne star input profile,
          largestEndpoint data hc hab hOne star input profile} ∧
      firstEndpoint data hc hab hOne star input profile =
        secondEndpoint data hc hab hOne star input profile ∧
      Incident data internal (firstEndpoint data hc hab hOne star input profile) ∧
      Incident data internal (largestEndpoint data hc hab hOne star input profile) ∧
      nonDanglingValency data
          (firstEndpoint data hc hab hOne star input profile) = 3 ∧
      nonDanglingValency data
          (largestEndpoint data hc hab hOne star input profile) = 2 := by
  classical
  have hVertex := selectedVertex_eq_mergedVertex data hc hab hOne star input
  have hWallNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) = 3 := by
    rw [← hVertex]
    exact profile_valency profile
  have hFirstWall : Incident (contractDatum data hc hab hOne) profile.first.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.first.2
  have hSecondWall : Incident (contractDatum data hc hab hOne) profile.second.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.second.2
  have hLargestWall : Incident (contractDatum data hc hab hOne) profile.largest.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.largest.2
  have hFirstActive : firstEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.first.1, profile_first_survives profile⟩ hFirstWall
  have hSecondActive : secondEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.second.1, profile_second_survives profile⟩ hSecondWall
  have hLargestActive : largestEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.largest.1, profile_largest_survives profile⟩ hLargestWall
  -- the largest survivor is restored to the trivalent original endpoint
  have hSideNe : IncomingTargetExpansion.right hc hab hOne profile.largest.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.largest)
      (by rw [hShared]; exact Ne.symm profile.first_target_ne)
  have hChangeV : data.targetChange
      (largestEndpoint data hc hab hOne star input profile).1.1 = 0 :=
    targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
      profile.largest.1 hSideNe
  have hSideV : (largestEndpoint data hc hab hOne star input profile).1.1 = a ∨
      (largestEndpoint data hc hab hOne star input profile).1.1 = b :=
    endpoint_target_mem data hc hab hOne profile.largest.1
  have hFirstNeV : (firstEndpoint data hc hab hOne star input profile).1.1 ≠
      (largestEndpoint data hc hab hOne star input profile).1.1 := by
    intro hEq
    refine hSideNe (((endpoint_target_eq_iff data hc hab hOne profile.largest.1
      profile.first.1).mp hEq.symm).trans ?_)
    rw [hShared]
  have hSecondTarget : (secondEndpoint data hc hab hOne star input profile).1.1 =
      (firstEndpoint data hc hab hOne star input profile).1.1 :=
    (endpoint_target_eq_iff data hc hab hOne profile.second.1 profile.first.1).mpr
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hSame.symm)
  -- at most one active constituent above the divalent endpoint
  have hOtherLe := otherSide_card_le_one data hc hab hOne fullDim hForest hCompat
    (selectedBlock data hc hab hOne star input) hWallNd
    (largestEndpoint data hc hab hOne star input profile).1.1 hSideV hChangeV
  have hFirstMemOther : firstEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (largestEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hFirstActive, hFirstNeV⟩
  have hSecondMemOther : secondEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (largestEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hSecondActive, by rw [hSecondTarget]; exact hFirstNeV⟩
  have hFirstEqSecond : firstEndpoint data hc hab hOne star input profile =
      secondEndpoint data hc hab hOne star input profile :=
    Finset.card_le_one.mp hOtherLe _ hFirstMemOther _ hSecondMemOther
  have hOtherSingleton : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (largestEndpoint data hc hab hOne star input profile).1.1) =
      {firstEndpoint data hc hab hOne star input profile} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hFirstMemOther,
      fun point hPoint ↦ Finset.card_le_one.mp hOtherLe _ hPoint _ hFirstMemOther⟩
  have hInternalInc : ∀ edge ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)),
      Incident data edge (firstEndpoint data hc hab hOne star input profile) :=
    fun edge hEdge ↦ internal_incident_otherEnd data hc hab hOne _ _ hSideV _
      hOtherSingleton edge hEdge
  -- the branch vertex already carries the two retained wall occurrences
  have hEmbNe : sourceEdgeEmbedding data hc hab hOne profile.first.1 ≠
      sourceEdgeEmbedding data hc hab hOne profile.second.1 :=
    embedding_ne data hc hab hOne hCompat.1
      ⟨profile.first.1, profile_first_survives profile⟩
      ⟨profile.second.1, profile_second_survives profile⟩
      (fun h ↦ profile.first_ne_second (Subtype.ext (congrArg
        (fun edge : NonDanglingEdge (contractDatum data hc hab hOne) ↦ edge.1) h)))
  have hExtra : ∀ edge ∈ ({sourceEdgeEmbedding data hc hab hOne profile.first.1,
        sourceEdgeEmbedding data hc hab hOne profile.second.1} :
        Finset data.SourceEdge),
      (¬ IsDangling data edge) ∧
        Incident data edge (firstEndpoint data hc hab hOne star input profile) ∧
        edge.1.1 ≠ contracted := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact ⟨(nonDanglingEmbedding data hCompat.1
          ⟨profile.first.1, profile_first_survives profile⟩).2,
        endpoint_incident data hc hab hOne
          (selectedBlock data hc hab hOne star input) profile.first.1 hFirstWall,
        sourceEdgeEmbedding_ne_contracted data hc hab hOne profile.first.1⟩
    · rcases Finset.mem_singleton.mp hEdge with rfl
      refine ⟨(nonDanglingEmbedding data hCompat.1
          ⟨profile.second.1, profile_second_survives profile⟩).2, ?_,
        sourceEdgeEmbedding_ne_contracted data hc hab hOne profile.second.1⟩
      rw [hFirstEqSecond]
      exact endpoint_incident data hc hab hOne
        (selectedBlock data hc hab hOne star input) profile.second.1 hSecondWall
  have hBound := extra_add_internal_card_le data hc hab hOne
    (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input))
    (firstEndpoint data hc hab hOne star input profile) hInternalInc _ hExtra
  rw [Finset.card_pair hEmbNe] at hBound
  have hFirstLe : nonDanglingValency data
      (firstEndpoint data hc hab hOne star input profile) ≤ 3 := by
    rcases active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
      (selectedBlock data hc hab hOne star input) hWallNd
      (firstEndpoint data hc hab hOne star input profile) hFirstActive with h | h <;>
      omega
  -- the pruned tree count
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
    hForest (selectedBlock data hc hab hOne star input)
    (activeFibre_nonempty data hc hab hOne hCompat
      (selectedBlock data hc hab hOne star input) hWallNd)
  have hSplit : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (largestEndpoint data hc hab hOne star input profile).1.1).card +
      ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (largestEndpoint data hc hab hOne star input profile).1.1).card =
      (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).card :=
    Finset.card_filter_add_card_filter_not _
  have hOtherCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (largestEndpoint data hc hab hOne star input profile).1.1).card = 1 := by
    rw [hOtherSingleton, Finset.card_singleton]
  have hLargestMemSide : largestEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (largestEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hLargestActive, rfl⟩
  have hSidePos : 1 ≤ ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (largestEndpoint data hc hab hOne star input profile).1.1).card :=
    Finset.card_pos.mpr ⟨_, hLargestMemSide⟩
  have hInternalCard : (internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 1 := by omega
  have hSideCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (largestEndpoint data hc hab hOne star input profile).1.1).card = 1 := by omega
  have hSideSingleton : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (largestEndpoint data hc hab hOne star input profile).1.1) =
      {largestEndpoint data hc hab hOne star input profile} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hLargestMemSide,
      fun point hPoint ↦ Finset.card_le_one.mp hSideCard.le _ hPoint _ hLargestMemSide⟩
  obtain ⟨internal, hInternal⟩ := Finset.card_eq_one.mp hInternalCard
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [hInternal]
    exact Finset.mem_singleton_self internal
  have hEndpointsNe : firstEndpoint data hc hab hOne star input profile ≠
      largestEndpoint data hc hab hOne star input profile :=
    fun h ↦ hFirstNeV (congrArg (fun point : data.SourceVertex ↦ point.1.1) h)
  have hActiveCard : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 2 := by omega
  have hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {firstEndpoint data hc hab hOne star input profile,
        largestEndpoint data hc hab hOne star input profile} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro point hPoint
      rcases Finset.mem_insert.mp hPoint with rfl | hPoint
      · exact hFirstActive
      · exact (Finset.mem_singleton.mp hPoint) ▸ hLargestActive
    · rw [hActiveCard, Finset.card_pair hEndpointsNe]
  have hIncFirst := hInternalInc internal hInternalMem
  have hIncLargest := internal_incident_sideEnd data hc hab hOne _ _ hSideV _
    hSideSingleton internal hInternalMem
  have hNdFirst : nonDanglingValency data
      (firstEndpoint data hc hab hOne star input profile) = 3 := by
    rw [hInternalCard] at hBound
    omega
  have hNdLargest : nonDanglingValency data
      (largestEndpoint data hc hab hOne star input profile) = 2 := by
    rcases active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
      (selectedBlock data hc hab hOne star input) hWallNd
      (largestEndpoint data hc hab hOne star input profile) hLargestActive with h | h
    · exact h
    · exact absurd h (active_valency_three_unique data hc hab hOne fullDim hForest
        hCompat (selectedBlock data hc hab hOne star input) hWallNd
        (firstEndpoint data hc hab hOne star input profile)
        (largestEndpoint data hc hab hOne star input profile) hFirstActive
        hLargestActive hEndpointsNe hNdFirst)
  rw [← hVertex] at hInternal hActive
  exact ⟨internal, hInternal, hActive, hFirstEqSecond, hIncFirst, hIncLargest,
    hNdFirst, hNdLargest⟩


/-- **Figure 30's `M⁽²⁾` orientation (`α = 4`), exact fibre census.**

If the unique retained wall direction at the divalent original endpoint is the
**largest** direction `t₄`, then `e₄` is restored there and its canonical
endpoint is the trivalent branch vertex, while the two smaller survivors `e₂`,
`e₃` are restored to the other endpoint with **distinct** divalent canonical
endpoints.  The selected pruned fibre is a path of **two** surviving
occurrences: the two new occurrences `e'`, `e''` of Figure 30's `M⁽²⁾`.

This is the first of the three nd3/nd2 divergences made explicit: nd2's fine
member has one surviving new occurrence and one dangling companion, whereas
`k₂ + k₃ = |A₀|` leaves no residual sheet and both new occurrences survive. -/
theorem selected_fibre_census_of_largest
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star =
      profile.largest.1.1.1) :
    ∃ first second : data.SourceEdge,
      first ≠ second ∧
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {first, second} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {largestEndpoint data hc hab hOne star input profile,
          firstEndpoint data hc hab hOne star input profile,
          secondEndpoint data hc hab hOne star input profile} ∧
      firstEndpoint data hc hab hOne star input profile ≠
        secondEndpoint data hc hab hOne star input profile ∧
      Incident data first (largestEndpoint data hc hab hOne star input profile) ∧
      Incident data first (firstEndpoint data hc hab hOne star input profile) ∧
      Incident data second (largestEndpoint data hc hab hOne star input profile) ∧
      Incident data second (secondEndpoint data hc hab hOne star input profile) ∧
      nonDanglingValency data
          (largestEndpoint data hc hab hOne star input profile) = 3 ∧
      nonDanglingValency data
          (firstEndpoint data hc hab hOne star input profile) = 2 ∧
      nonDanglingValency data
          (secondEndpoint data hc hab hOne star input profile) = 2 := by
  classical
  have hVertex := selectedVertex_eq_mergedVertex data hc hab hOne star input
  have hWallNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) = 3 := by
    rw [← hVertex]
    exact profile_valency profile
  have hFirstWall : Incident (contractDatum data hc hab hOne) profile.first.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.first.2
  have hSecondWall : Incident (contractDatum data hc hab hOne) profile.second.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.second.2
  have hLargestWall : Incident (contractDatum data hc hab hOne) profile.largest.1
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) := by
    rw [← hVertex]
    exact profile.largest.2
  have hFirstActive : firstEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.first.1, profile_first_survives profile⟩ hFirstWall
  have hSecondActive : secondEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.second.1, profile_second_survives profile⟩ hSecondWall
  have hLargestActive : largestEndpoint data hc hab hOne star input profile ∈
      activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input)) :=
    endpoint_active data hc hab hOne hCompat.1
      (selectedBlock data hc hab hOne star input)
      ⟨profile.largest.1, profile_largest_survives profile⟩ hLargestWall
  -- the doubled direction is restored to the trivalent original endpoint
  have hSideNe : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.first)
      (by rw [hLargest]; exact profile.first_target_ne)
  have hChangeV : data.targetChange
      (firstEndpoint data hc hab hOne star input profile).1.1 = 0 :=
    targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
      profile.first.1 hSideNe
  have hSideV : (firstEndpoint data hc hab hOne star input profile).1.1 = a ∨
      (firstEndpoint data hc hab hOne star input profile).1.1 = b :=
    endpoint_target_mem data hc hab hOne profile.first.1
  have hSecondTarget : (secondEndpoint data hc hab hOne star input profile).1.1 =
      (firstEndpoint data hc hab hOne star input profile).1.1 :=
    (endpoint_target_eq_iff data hc hab hOne profile.second.1 profile.first.1).mpr
      (congrArg (IncomingTargetExpansion.right hc hab hOne) hSame.symm)
  have hLargestNeV : (largestEndpoint data hc hab hOne star input profile).1.1 ≠
      (firstEndpoint data hc hab hOne star input profile).1.1 := by
    intro hEq
    refine hSideNe ?_
    rw [hLargest]
    exact ((endpoint_target_eq_iff data hc hab hOne profile.first.1
      profile.largest.1).mp hEq.symm)
  -- the two smaller survivors cannot share a canonical endpoint
  have hEmbNe : sourceEdgeEmbedding data hc hab hOne profile.first.1 ≠
      sourceEdgeEmbedding data hc hab hOne profile.second.1 :=
    embedding_ne data hc hab hOne hCompat.1
      ⟨profile.first.1, profile_first_survives profile⟩
      ⟨profile.second.1, profile_second_survives profile⟩
      (fun h ↦ profile.first_ne_second (Subtype.ext (congrArg
        (fun edge : NonDanglingEdge (contractDatum data hc hab hOne) ↦ edge.1) h)))
  have hFirstNeSecond : firstEndpoint data hc hab hOne star input profile ≠
      secondEndpoint data hc hab hOne star input profile := by
    intro hEq
    refine hEmbNe (sourceEdge_eq_of_same_target_unramified data fullDim
      (firstEndpoint data hc hab hOne star input profile) hChangeV
      (active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
        (selectedBlock data hc hab hOne star input) hWallNd
        (firstEndpoint data hc hab hOne star input profile) hFirstActive)
      (sourceEdgeEmbedding data hc hab hOne profile.first.1)
      (sourceEdgeEmbedding data hc hab hOne profile.second.1)
      (nonDanglingEmbedding data hCompat.1
        ⟨profile.first.1, profile_first_survives profile⟩).2
      (nonDanglingEmbedding data hCompat.1
        ⟨profile.second.1, profile_second_survives profile⟩).2
      (endpoint_incident data hc hab hOne
        (selectedBlock data hc hab hOne star input) profile.first.1 hFirstWall)
      ?_ ?_)
    · rw [hEq]
      exact endpoint_incident data hc hab hOne
        (selectedBlock data hc hab hOne star input) profile.second.1 hSecondWall
    · rw [embedding_target, embedding_target, hSame]
  -- the branch vertex is the unique active constituent above the divalent endpoint
  have hOtherLe := otherSide_card_le_one data hc hab hOne fullDim hForest hCompat
    (selectedBlock data hc hab hOne star input) hWallNd
    (firstEndpoint data hc hab hOne star input profile).1.1 hSideV hChangeV
  have hLargestMemOther : largestEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (firstEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hLargestActive, hLargestNeV⟩
  have hOtherSingleton : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ ¬ point.1.1 =
          (firstEndpoint data hc hab hOne star input profile).1.1) =
      {largestEndpoint data hc hab hOne star input profile} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hLargestMemOther,
      fun point hPoint ↦ Finset.card_le_one.mp hOtherLe _ hPoint _ hLargestMemOther⟩
  have hInternalInc : ∀ edge ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)),
      Incident data edge (largestEndpoint data hc hab hOne star input profile) :=
    fun edge hEdge ↦ internal_incident_otherEnd data hc hab hOne _ _ hSideV _
      hOtherSingleton edge hEdge
  have hExtra : ∀ edge ∈ ({sourceEdgeEmbedding data hc hab hOne profile.largest.1} :
        Finset data.SourceEdge),
      (¬ IsDangling data edge) ∧
        Incident data edge (largestEndpoint data hc hab hOne star input profile) ∧
        edge.1.1 ≠ contracted := by
    intro edge hEdge
    rcases Finset.mem_singleton.mp hEdge with rfl
    exact ⟨(nonDanglingEmbedding data hCompat.1
        ⟨profile.largest.1, profile_largest_survives profile⟩).2,
      endpoint_incident data hc hab hOne
        (selectedBlock data hc hab hOne star input) profile.largest.1 hLargestWall,
      sourceEdgeEmbedding_ne_contracted data hc hab hOne profile.largest.1⟩
  have hBound := extra_add_internal_card_le data hc hab hOne
    (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input))
    (largestEndpoint data hc hab hOne star input profile) hInternalInc _ hExtra
  rw [Finset.card_singleton] at hBound
  have hLargestLe : nonDanglingValency data
      (largestEndpoint data hc hab hOne star input profile) ≤ 3 := by
    rcases active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
      (selectedBlock data hc hab hOne star input) hWallNd
      (largestEndpoint data hc hab hOne star input profile) hLargestActive with h | h <;>
      omega
  -- the pruned tree count
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
    hForest (selectedBlock data hc hab hOne star input)
    (activeFibre_nonempty data hc hab hOne hCompat
      (selectedBlock data hc hab hOne star input) hWallNd)
  have hSplit : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input profile).1.1).card +
      ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (firstEndpoint data hc hab hOne star input profile).1.1).card =
      (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).card :=
    Finset.card_filter_add_card_filter_not _
  have hOtherCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ ¬ point.1.1 =
        (firstEndpoint data hc hab hOne star input profile).1.1).card = 1 := by
    rw [hOtherSingleton, Finset.card_singleton]
  have hPairSubset : ({firstEndpoint data hc hab hOne star input profile,
        secondEndpoint data hc hab hOne star input profile} :
        Finset data.SourceVertex) ⊆
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (firstEndpoint data hc hab hOne star input profile).1.1) := by
    intro point hPoint
    rcases Finset.mem_insert.mp hPoint with rfl | hPoint
    · exact Finset.mem_filter.mpr ⟨hFirstActive, rfl⟩
    · exact (Finset.mem_singleton.mp hPoint) ▸
        Finset.mem_filter.mpr ⟨hSecondActive, hSecondTarget⟩
  have hSideGe : 2 ≤ ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input profile).1.1).card := by
    have := Finset.card_le_card hPairSubset
    rwa [Finset.card_pair hFirstNeSecond] at this
  have hInternalCard : (internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 2 := by omega
  have hSideCard : ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne
          (selectedBlock data hc hab hOne star input))).filter
      fun point ↦ point.1.1 =
        (firstEndpoint data hc hab hOne star input profile).1.1).card = 2 := by omega
  have hActiveCard : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).card = 3 := by omega
  -- the two internal occurrences, named by the endpoints they reach
  have hImage := sideEnd_image data hc hab hOne fullDim hForest hCompat
    (selectedBlock data hc hab hOne star input) hWallNd
    (firstEndpoint data hc hab hOne star input profile).1.1 hSideV hChangeV (by omega)
  have hFirstMemSide : firstEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (firstEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hFirstActive, rfl⟩
  have hSecondMemSide : secondEndpoint data hc hab hOne star input profile ∈
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne
        (selectedBlock data hc hab hOne star input))).filter
        (fun point ↦ point.1.1 =
          (firstEndpoint data hc hab hOne star input profile).1.1) :=
    Finset.mem_filter.mpr ⟨hSecondActive, hSecondTarget⟩
  rw [← hImage] at hFirstMemSide hSecondMemSide
  obtain ⟨firstInternal, hFirstInternalMem, hFirstInternalEnd⟩ :=
    Finset.mem_image.mp hFirstMemSide
  obtain ⟨secondInternal, hSecondInternalMem, hSecondInternalEnd⟩ :=
    Finset.mem_image.mp hSecondMemSide
  have hInternalNe : firstInternal ≠ secondInternal := by
    intro hEq
    exact hFirstNeSecond (hFirstInternalEnd.symm.trans
      ((congrArg (sideEnd data
        (firstEndpoint data hc hab hOne star input profile).1.1) hEq).trans
        hSecondInternalEnd))
  have hInternal : internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {firstInternal, secondInternal} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact hFirstInternalMem
      · exact (Finset.mem_singleton.mp hEdge) ▸ hSecondInternalMem
    · rw [hInternalCard, Finset.card_pair hInternalNe]
  -- the active census
  have hLargestNeFirst : largestEndpoint data hc hab hOne star input profile ≠
      firstEndpoint data hc hab hOne star input profile :=
    fun h ↦ hLargestNeV (congrArg (fun point : data.SourceVertex ↦ point.1.1) h)
  have hLargestNeSecond : largestEndpoint data hc hab hOne star input profile ≠
      secondEndpoint data hc hab hOne star input profile := by
    intro h
    exact hLargestNeV ((congrArg (fun point : data.SourceVertex ↦ point.1.1) h).trans
      hSecondTarget)
  have hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {largestEndpoint data hc hab hOne star input profile,
        firstEndpoint data hc hab hOne star input profile,
        secondEndpoint data hc hab hOne star input profile} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro point hPoint
      rcases Finset.mem_insert.mp hPoint with rfl | hPoint
      · exact hLargestActive
      · rcases Finset.mem_insert.mp hPoint with rfl | hPoint
        · exact hFirstActive
        · exact (Finset.mem_singleton.mp hPoint) ▸ hSecondActive
    · rw [hActiveCard, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h ↦ h.elim hLargestNeFirst hLargestNeSecond),
        Finset.card_pair hFirstNeSecond]
  -- valencies
  have hNdLargest : nonDanglingValency data
      (largestEndpoint data hc hab hOne star input profile) = 3 := by
    rw [hInternalCard] at hBound
    omega
  have hNdFirst : nonDanglingValency data
      (firstEndpoint data hc hab hOne star input profile) = 2 := by
    rcases active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
      (selectedBlock data hc hab hOne star input) hWallNd
      (firstEndpoint data hc hab hOne star input profile) hFirstActive with h | h
    · exact h
    · exact absurd h (active_valency_three_unique data hc hab hOne fullDim hForest
        hCompat (selectedBlock data hc hab hOne star input) hWallNd
        (largestEndpoint data hc hab hOne star input profile)
        (firstEndpoint data hc hab hOne star input profile) hLargestActive
        hFirstActive hLargestNeFirst hNdLargest)
  have hNdSecond : nonDanglingValency data
      (secondEndpoint data hc hab hOne star input profile) = 2 := by
    rcases active_valency_two_or_three data hc hab hOne fullDim hForest hCompat
      (selectedBlock data hc hab hOne star input) hWallNd
      (secondEndpoint data hc hab hOne star input profile) hSecondActive with h | h
    · exact h
    · exact absurd h (active_valency_three_unique data hc hab hOne fullDim hForest
        hCompat (selectedBlock data hc hab hOne star input) hWallNd
        (largestEndpoint data hc hab hOne star input profile)
        (secondEndpoint data hc hab hOne star input profile) hLargestActive
        hSecondActive hLargestNeSecond hNdLargest)
  rw [← hVertex] at hInternal hActive
  refine ⟨firstInternal, secondInternal, hInternalNe, hInternal, hActive,
    hFirstNeSecond, hInternalInc firstInternal hFirstInternalMem, ?_,
    hInternalInc secondInternal hSecondInternalMem, ?_, hNdLargest, hNdFirst, hNdSecond⟩
  · exact hFirstInternalEnd ▸ sideEnd_incident data _ firstInternal
  · exact hSecondInternalEnd ▸ sideEnd_incident data _ secondInternal


/-! ## Sheet classes -/

end Selected

/-- **The two Figure 30 steps at one active triple.**  Each unramified
endpoint is Case (r0-nd2) and fixes the class of the internal occurrence
reaching it; refinement of both internal occurrences into the branch vertex
then collapses the non-dangling union `A₀ = A⁽ᑫ⁾ ∪ A' ∪ A''` onto the branch
vertex.  This is the three-constituent analogue of
`W3Nd2IncomingSheetClasses.sheet_classes_of_active_pair`, needed because the
`M⁽²⁾` fibre is a path rather than a single occurrence. -/
theorem sheet_classes_of_active_triple
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (block : (mergedPartition data a b).Blocks)
    (firstInternal secondInternal : data.SourceEdge)
    (branch first second : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) = {branch, first, second})
    (hFirstInternal : firstInternal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hSecondInternal : secondInternal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hFirstBranch : Incident data firstInternal branch)
    (hFirstEnd : Incident data firstInternal first)
    (hSecondBranch : Incident data secondInternal branch)
    (hSecondEnd : Incident data secondInternal second)
    (hFirstNd : nonDanglingValency data first = 2)
    (hFirstChange : data.targetChange first.1.1 = 0)
    (hSecondNd : nonDanglingValency data second = 2)
    (hSecondChange : data.targetChange second.1.1 = 0) :
    (data.edgePartition firstInternal.1.1).block firstInternal.1.2 =
        (data.vertexPartition first.1.1).block first.1.2 ∧
      (data.edgePartition secondInternal.1.1).block secondInternal.1.2 =
        (data.vertexPartition second.1.1).block second.1.2 ∧
      (data.vertexPartition branch.1.1).block branch.1.2 =
        (mergedPartition data a b).block block.1 := by
  classical
  have hFirstSurvives :=
    ((mem_internalEdges data hc hab hOne _ firstInternal).mp hFirstInternal).1
  have hSecondSurvives :=
    ((mem_internalEdges data hc hab hOne _ secondInternal).mp hSecondInternal).1
  have hFirstBlock := W4IncomingCensus.block_eq_of_survives_nd2_r0 data
    fullDim.danglingEdgeNoGlue first hFirstNd
    (localRamification_endpoint_eq_zero data fullDim first _ rfl hFirstChange)
    firstInternal hFirstSurvives hFirstEnd
  have hSecondBlock := W4IncomingCensus.block_eq_of_survives_nd2_r0 data
    fullDim.danglingEdgeNoGlue second hSecondNd
    (localRamification_endpoint_eq_zero data fullDim second _ rfl hSecondChange)
    secondInternal hSecondSurvives hSecondEnd
  have hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := by
    rw [hActive]
    exact Finset.insert_nonempty branch _
  have hUnion := block_eq_active_union_local data fullDim hc hab hOne block hNonempty
  rw [hActive, Finset.biUnion_insert, Finset.biUnion_insert,
    Finset.singleton_biUnion] at hUnion
  have hRefine : ∀ edge : data.SourceEdge, Incident data edge branch →
      (data.edgePartition edge.1.1).block edge.1.2 ⊆
        (data.vertexPartition branch.1.1).block branch.1.2 := by
    intro edge hIncident
    obtain ⟨hAt, hRel⟩ := (incident_iff_target_mem_and_rel data edge branch).mp hIncident
    intro sheet hSheet
    exact (SheetPartition.mem_block_iff _ _ _).mpr
      (hRel.trans ((refines_of_mem_incidentEdges data hAt).rel
        ((SheetPartition.mem_block_iff _ _ _).mp hSheet)))
  have hFirstSubset : (data.vertexPartition first.1.1).block first.1.2 ⊆
      (data.vertexPartition branch.1.1).block branch.1.2 := by
    rw [← hFirstBlock]
    exact hRefine firstInternal hFirstBranch
  have hSecondSubset : (data.vertexPartition second.1.1).block second.1.2 ⊆
      (data.vertexPartition branch.1.1).block branch.1.2 := by
    rw [← hSecondBlock]
    exact hRefine secondInternal hSecondBranch
  refine ⟨hFirstBlock, hSecondBlock, ?_⟩
  rw [Finset.union_eq_left.mpr (Finset.union_subset hFirstSubset hSecondSubset)] at hUnion
  exact hUnion.symm

section Classes

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)

include fullDim hForest hCompat

/-- **Figure 30's `M⁽¹⁾` selected sheet classes.**  The single internal
occurrence, the largest survivor's canonical endpoint and that survivor's own
retained wall flag all carry one and the same literal sheet set, and the branch
vertex — the common canonical endpoint of the two smaller survivors — carries
the entire merged wall class `A₀`. -/
theorem selected_sheet_classes_of_shared
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hShared : divalentOccurrence data hc hab hOne fullDim star =
      profile.first.1.1.1) :
    ∃ internal : data.SourceEdge,
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {internal} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {firstEndpoint data hc hab hOne star input profile,
          largestEndpoint data hc hab hOne star input profile} ∧
      firstEndpoint data hc hab hOne star input profile =
        secondEndpoint data hc hab hOne star input profile ∧
      Incident data internal (firstEndpoint data hc hab hOne star input profile) ∧
      Incident data internal (largestEndpoint data hc hab hOne star input profile) ∧
      (data.edgePartition internal.1.1).block internal.1.2 =
        (data.vertexPartition
            (largestEndpoint data hc hab hOne star input profile).1.1).block
          (largestEndpoint data hc hab hOne star input profile).1.2 ∧
      (data.vertexPartition
            (largestEndpoint data hc hab hOne star input profile).1.1).block
          (largestEndpoint data hc hab hOne star input profile).1.2 =
        ((contractDatum data hc hab hOne).edgePartition
            profile.largest.1.1.1).block profile.largest.1.1.2 ∧
      (data.vertexPartition
            (firstEndpoint data hc hab hOne star input profile).1.1).block
          (firstEndpoint data hc hab hOne star input profile).1.2 =
        (mergedPartition data a b).block
          (selectedBlock data hc hab hOne star input).1 ∧
      nonDanglingValency data
          (firstEndpoint data hc hab hOne star input profile) = 3 ∧
      nonDanglingValency data
          (largestEndpoint data hc hab hOne star input profile) = 2 := by
  classical
  obtain ⟨internal, hInternal, hActive, hEndpointEq, hIncFirst, hIncLargest,
    hNdFirst, hNdLargest⟩ :=
    selected_fibre_census_of_shared data hc hab hOne fullDim hForest hCompat star input
      profile hSame hShared
  have hSideNe : IncomingTargetExpansion.right hc hab hOne profile.largest.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.largest)
      (by rw [hShared]; exact Ne.symm profile.first_target_ne)
  have hChange : data.targetChange
      (largestEndpoint data hc hab hOne star input profile).1.1 = 0 :=
    targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
      profile.largest.1 hSideNe
  have hActiveMerged : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {firstEndpoint data hc hab hOne star input profile,
        largestEndpoint data hc hab hOne star input profile} := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
    exact hActive
  have hInternalMem : internal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hInternal]
    exact Finset.mem_singleton_self internal
  obtain ⟨hInternalClass, hBranchClass⟩ := sheet_classes_of_active_pair data fullDim
    hc hab hOne (selectedBlock data hc hab hOne star input) internal
    (firstEndpoint data hc hab hOne star input profile)
    (largestEndpoint data hc hab hOne star input profile)
    hActiveMerged hInternalMem hIncFirst hIncLargest hNdLargest hChange
  have hFlag := endpoint_block_eq_flag_local data fullDim hc hab hOne hCompat.1
    (selectedBlock data hc hab hOne star input)
    ⟨profile.largest.1, profile_largest_survives profile⟩
    (by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.largest.2)
    hNdLargest hChange
  exact ⟨internal, hInternal, hActive, hEndpointEq, hIncFirst, hIncLargest,
    hInternalClass, hFlag, hBranchClass, hNdFirst, hNdLargest⟩

/-- **Figure 30's `M⁽²⁾` selected sheet classes.**  The two internal
occurrences `e'`, `e''` carry the sheet classes of the two smaller survivors'
distinct canonical endpoints, which are in turn those survivors' own retained
wall flags, and the branch vertex — the largest survivor's canonical endpoint —
carries the entire merged wall class `A₀`. -/
theorem selected_sheet_classes_of_largest
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (hLargest : divalentOccurrence data hc hab hOne fullDim star =
      profile.largest.1.1.1) :
    ∃ first second : data.SourceEdge,
      first ≠ second ∧
      internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
          {first, second} ∧
      activeFibreVertices data hc hab hOne
          (selectedVertex data hc hab hOne star input) =
        {largestEndpoint data hc hab hOne star input profile,
          firstEndpoint data hc hab hOne star input profile,
          secondEndpoint data hc hab hOne star input profile} ∧
      firstEndpoint data hc hab hOne star input profile ≠
        secondEndpoint data hc hab hOne star input profile ∧
      Incident data first (largestEndpoint data hc hab hOne star input profile) ∧
      Incident data first (firstEndpoint data hc hab hOne star input profile) ∧
      Incident data second (largestEndpoint data hc hab hOne star input profile) ∧
      Incident data second (secondEndpoint data hc hab hOne star input profile) ∧
      (data.edgePartition first.1.1).block first.1.2 =
        (data.vertexPartition
            (firstEndpoint data hc hab hOne star input profile).1.1).block
          (firstEndpoint data hc hab hOne star input profile).1.2 ∧
      (data.edgePartition second.1.1).block second.1.2 =
        (data.vertexPartition
            (secondEndpoint data hc hab hOne star input profile).1.1).block
          (secondEndpoint data hc hab hOne star input profile).1.2 ∧
      (data.vertexPartition
            (firstEndpoint data hc hab hOne star input profile).1.1).block
          (firstEndpoint data hc hab hOne star input profile).1.2 =
        ((contractDatum data hc hab hOne).edgePartition
            profile.first.1.1.1).block profile.first.1.1.2 ∧
      (data.vertexPartition
            (secondEndpoint data hc hab hOne star input profile).1.1).block
          (secondEndpoint data hc hab hOne star input profile).1.2 =
        ((contractDatum data hc hab hOne).edgePartition
            profile.second.1.1.1).block profile.second.1.1.2 ∧
      (data.vertexPartition
            (largestEndpoint data hc hab hOne star input profile).1.1).block
          (largestEndpoint data hc hab hOne star input profile).1.2 =
        (mergedPartition data a b).block
          (selectedBlock data hc hab hOne star input).1 ∧
      nonDanglingValency data
          (largestEndpoint data hc hab hOne star input profile) = 3 ∧
      nonDanglingValency data
          (firstEndpoint data hc hab hOne star input profile) = 2 ∧
      nonDanglingValency data
          (secondEndpoint data hc hab hOne star input profile) = 2 := by
  classical
  obtain ⟨firstInternal, secondInternal, hInternalNe, hInternal, hActive,
    hEndpointNe, hFirstBranch, hFirstEnd, hSecondBranch, hSecondEnd,
    hNdLargest, hNdFirst, hNdSecond⟩ :=
    selected_fibre_census_of_largest data hc hab hOne fullDim hForest hCompat star input
      profile hSame hLargest
  have hSideNe : IncomingTargetExpansion.right hc hab hOne profile.first.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) :=
    side_ne_of_ne_divalentOccurrence data hc hab hOne fullDim star _
      (W3Nd3SourceCandidates.incident_target_mem input profile.first)
      (by rw [hLargest]; exact profile.first_target_ne)
  have hSecondSideNe : IncomingTargetExpansion.right hc hab hOne profile.second.1.1.1 ≠
      IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) := by
    rw [← hSame]
    exact hSideNe
  have hFirstChange : data.targetChange
      (firstEndpoint data hc hab hOne star input profile).1.1 = 0 :=
    targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
      profile.first.1 hSideNe
  have hSecondChange : data.targetChange
      (secondEndpoint data hc hab hOne star input profile).1.1 = 0 :=
    targetChange_endpoint_eq_zero_of_side_ne data fullDim hc hab hOne star
      profile.second.1 hSecondSideNe
  have hActiveMerged : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) =
      {largestEndpoint data hc hab hOne star input profile,
        firstEndpoint data hc hab hOne star input profile,
        secondEndpoint data hc hab hOne star input profile} := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
    exact hActive
  have hFirstInternalMem : firstInternal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hInternal]
    exact Finset.mem_insert_self _ _
  have hSecondInternalMem : secondInternal ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne (selectedBlock data hc hab hOne star input)) := by
    rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input, hInternal]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hFirstClass, hSecondClass, hBranchClass⟩ := sheet_classes_of_active_triple
    data fullDim hc hab hOne (selectedBlock data hc hab hOne star input)
    firstInternal secondInternal
    (largestEndpoint data hc hab hOne star input profile)
    (firstEndpoint data hc hab hOne star input profile)
    (secondEndpoint data hc hab hOne star input profile)
    hActiveMerged hFirstInternalMem hSecondInternalMem hFirstBranch hFirstEnd
    hSecondBranch hSecondEnd hNdFirst hFirstChange hNdSecond hSecondChange
  have hFirstFlag := endpoint_block_eq_flag_local data fullDim hc hab hOne hCompat.1
    (selectedBlock data hc hab hOne star input)
    ⟨profile.first.1, profile_first_survives profile⟩
    (by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.first.2)
    hNdFirst hFirstChange
  have hSecondFlag := endpoint_block_eq_flag_local data fullDim hc hab hOne hCompat.1
    (selectedBlock data hc hab hOne star input)
    ⟨profile.second.1, profile_second_survives profile⟩
    (by
      rw [← selectedVertex_eq_mergedVertex data hc hab hOne star input]
      exact profile.second.2)
    hNdSecond hSecondChange
  exact ⟨firstInternal, secondInternal, hInternalNe, hInternal, hActive, hEndpointNe,
    hFirstBranch, hFirstEnd, hSecondBranch, hSecondEnd, hFirstClass, hSecondClass,
    hFirstFlag, hSecondFlag, hBranchClass, hNdLargest, hNdFirst, hNdSecond⟩


/-- **The selected incoming nd3 fibre and its sheet classes, unconditional.**

Both Figure 30 orientations at once, for an arbitrary incoming W3 nd3 datum.
The dichotomy is discharged by `divalentOccurrence_eq_shared_or_largest`, and
both alternatives genuinely occur: they are `M⁽¹⁾` (`α = 3`) and `M⁽²⁾`
(`α = 4`).  In each the branch vertex of the selected fibre is the canonical
endpoint above the **divalent** original endpoint, it is trivalent, and its
literal sheet class is the whole merged wall class `A₀`; the remaining active
constituents are divalent, unramified, and carry the classes of the internal
occurrences and of their own retained wall flags.

This identifies the *classes*.  Matching them against the stored
representatives of the Figure 30 candidates through `PartitionNormalization`,
the `r = 0` background blocks, and the original-coordinate restatement are not
proved here (see `W3Nd3IncomingMatching` and `W3Nd3ArbitraryExit`). -/
theorem selected_sheet_classes
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (∃ internal : data.SourceEdge,
        internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
            {internal} ∧
        activeFibreVertices data hc hab hOne
            (selectedVertex data hc hab hOne star input) =
          {firstEndpoint data hc hab hOne star input profile,
            largestEndpoint data hc hab hOne star input profile} ∧
        firstEndpoint data hc hab hOne star input profile =
          secondEndpoint data hc hab hOne star input profile ∧
        Incident data internal (firstEndpoint data hc hab hOne star input profile) ∧
        Incident data internal (largestEndpoint data hc hab hOne star input profile) ∧
        (data.edgePartition internal.1.1).block internal.1.2 =
          (data.vertexPartition
              (largestEndpoint data hc hab hOne star input profile).1.1).block
            (largestEndpoint data hc hab hOne star input profile).1.2 ∧
        (data.vertexPartition
              (largestEndpoint data hc hab hOne star input profile).1.1).block
            (largestEndpoint data hc hab hOne star input profile).1.2 =
          ((contractDatum data hc hab hOne).edgePartition
              profile.largest.1.1.1).block profile.largest.1.1.2 ∧
        (data.vertexPartition
              (firstEndpoint data hc hab hOne star input profile).1.1).block
            (firstEndpoint data hc hab hOne star input profile).1.2 =
          (mergedPartition data a b).block
            (selectedBlock data hc hab hOne star input).1 ∧
        nonDanglingValency data
            (firstEndpoint data hc hab hOne star input profile) = 3 ∧
        nonDanglingValency data
            (largestEndpoint data hc hab hOne star input profile) = 2) ∨
    (∃ first second : data.SourceEdge,
        first ≠ second ∧
        internalEdges data hc hab hOne (selectedVertex data hc hab hOne star input) =
            {first, second} ∧
        activeFibreVertices data hc hab hOne
            (selectedVertex data hc hab hOne star input) =
          {largestEndpoint data hc hab hOne star input profile,
            firstEndpoint data hc hab hOne star input profile,
            secondEndpoint data hc hab hOne star input profile} ∧
        firstEndpoint data hc hab hOne star input profile ≠
          secondEndpoint data hc hab hOne star input profile ∧
        Incident data first (largestEndpoint data hc hab hOne star input profile) ∧
        Incident data first (firstEndpoint data hc hab hOne star input profile) ∧
        Incident data second (largestEndpoint data hc hab hOne star input profile) ∧
        Incident data second (secondEndpoint data hc hab hOne star input profile) ∧
        (data.edgePartition first.1.1).block first.1.2 =
          (data.vertexPartition
              (firstEndpoint data hc hab hOne star input profile).1.1).block
            (firstEndpoint data hc hab hOne star input profile).1.2 ∧
        (data.edgePartition second.1.1).block second.1.2 =
          (data.vertexPartition
              (secondEndpoint data hc hab hOne star input profile).1.1).block
            (secondEndpoint data hc hab hOne star input profile).1.2 ∧
        (data.vertexPartition
              (firstEndpoint data hc hab hOne star input profile).1.1).block
            (firstEndpoint data hc hab hOne star input profile).1.2 =
          ((contractDatum data hc hab hOne).edgePartition
              profile.first.1.1.1).block profile.first.1.1.2 ∧
        (data.vertexPartition
              (secondEndpoint data hc hab hOne star input profile).1.1).block
            (secondEndpoint data hc hab hOne star input profile).1.2 =
          ((contractDatum data hc hab hOne).edgePartition
              profile.second.1.1.1).block profile.second.1.1.2 ∧
        (data.vertexPartition
              (largestEndpoint data hc hab hOne star input profile).1.1).block
            (largestEndpoint data hc hab hOne star input profile).1.2 =
          (mergedPartition data a b).block
            (selectedBlock data hc hab hOne star input).1 ∧
        nonDanglingValency data
            (largestEndpoint data hc hab hOne star input profile) = 3 ∧
        nonDanglingValency data
            (firstEndpoint data hc hab hOne star input profile) = 2 ∧
        nonDanglingValency data
            (secondEndpoint data hc hab hOne star input profile) = 2) := by
  rcases divalentOccurrence_eq_shared_or_largest data hc hab hOne fullDim hForest
    hCompat star input profile hSame with hShared | hLargest
  · exact Or.inl (selected_sheet_classes_of_shared data hc hab hOne fullDim hForest
      hCompat star input profile hSame hShared)
  · exact Or.inr (selected_sheet_classes_of_largest data hc hab hOne fullDim hForest
      hCompat star input profile hSame hLargest)

end Classes



/-! ## The `r = 0` background blocks

Nothing in Case `{w3-r0}` sees the distinguished block's *profile*: a
background block is characterised by `background ≠ input.distinguishedBlock`,
its vanishing wall ramification comes from
`ThirdEquation.W3SourceInput.localRamification_eq_zero_of_ne`, and the divalent
dichotomy at the original endpoints comes from full-dimensionality and the
contraction forest.  `W3Nd2IncomingBackground` is stated for exactly that data
and therefore applies verbatim to an incoming **nd3** datum; the theorem below
is that application, recorded in the nd3 namespace so that the applicability is
machine-checked rather than asserted, and so that the other nd3 modules have
an nd3-named entry point.  The same is true of the stronger whole-block form
`W3Nd2IncomingNormalization.background_whole_block_census`, which is likewise
profile-free.  No nd3-specific background statement is needed or claimed. -/
theorem background_dichotomy
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hBackground : background ≠ input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    ((nonDanglingValency data (data.sourceEndpoint a sheet) = 0 ∧
          (data.vertexPartition a).block sheet = {sheet}) ∨
        (nonDanglingValency data (data.sourceEndpoint a sheet) = 2 ∧
          ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
            Incident data edge (data.sourceEndpoint a sheet) →
            (data.edgePartition edge.1.1).block edge.1.2 =
              (data.vertexPartition a).block sheet)) ∨
      ((nonDanglingValency data (data.sourceEndpoint b sheet) = 0 ∧
            (data.vertexPartition b).block sheet = {sheet}) ∨
          (nonDanglingValency data (data.sourceEndpoint b sheet) = 2 ∧
            ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
              Incident data edge (data.sourceEndpoint b sheet) →
              (data.edgePartition edge.1.1).block edge.1.2 =
                (data.vertexPartition b).block sheet)) :=
  W3Nd2IncomingBackground.background_dichotomy data hc hab hOne fullDim hForest input
    hBackground sheet hSheet

end DraismaVargas.LocalCases.W3Nd3IncomingCensus
