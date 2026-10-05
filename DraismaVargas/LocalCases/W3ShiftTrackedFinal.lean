module

public import DraismaVargas.LocalCases.W3ShiftGraphTracking

@[expose] public section

/-!
# Full source-facing Figure 29 tracking, including the two incoming branch swaps

The existing branch swaps are actual compatible sheet relabellings, so their
full-dimensional presentation and incidence certificate have the same literal
row map. The adjacent swap wrapper retains Tracks on that same presentation.
Position II.a follows the existing two-swap construction and the checked
tracked pair exit; classification derives both positional censuses. No row,
graph, or family-matching receipt is supplied at the final producer.
-/

namespace DraismaVargas.LocalCases.W3ShiftTrackedFinal

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification ContractionFibre
open W4StableSource W4Assembly ThirdEquation W3R1SourceProfile FullDimensionalSource
open WallDegeneration TargetExpansion InteriorGraphTracking
open W3ShiftSourceCandidates W3ShiftIncomingMatching W3ShiftLimitRows
open W3ShiftIncomingTransport W3ShiftClosureFinal W3ShiftGraphTracking
open W3Nd2IncomingTargetPlacement (divalentOccurrence)

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

universe u
variable {target : CFGraph.{u}} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- The exact row equation is definitional for the actual sheet relabelling's
presentation and incidence certificate, so tracking follows the same cover. -/
noncomputable def sheetPresentation_tracking
    {data : GluingDatum target degree}
    {fd : FullDimensionalSourcePresentation data coordinate}
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label) (relabeling : data.SheetRelabeling) :
    Tracks (RelabelFullDimensional.sheetPresentation relabeling fd) graph label :=
  throughIncidence current (RelabelFullDimensional.sheetPresentation relabeling fd)
    (StableGraphIncidence.sheetRelabel relabeling fd.connected) rfl

section Swap

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)

/-- **One of Figure 29's two clearing swaps, performed one level up.**  The
permutation `W3ShiftClosure.exists_branchSwapPerm_clearing_endpoint` chooses
inside a block of the trivalent endpoint's own partition, which is exactly
`W3ShiftIncomingTransport.EndsCompatible`, so the same swap can be performed on
the **incoming** datum before the contraction.  Everything the rest of the case reads
off the incoming cover survives: both endpoint partitions, the contracted
occurrence's partition, the contraction receipt, the stable incidence graph, the
length matrix, the column labelling and the divalent wall occurrence -- and the
contracted copy is literally `W3ShiftClosure.clearData`, i.e. the wall-level
gauge copy the pair is built over. -/
theorem exists_tracked_incoming_swap
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (divalent direction : (contract target hab hOne).edges)
    (hDivalent : divalentOccurrence data hc hab hOne fullDim star = divalent)
    (hDivalentMem : divalent ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirMem : direction ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hDirNe : divalent ≠ direction)
    (hOnly : ∀ e ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V),
      IncomingTargetExpansion.right hc hab hOne e =
        IncomingTargetExpansion.right hc hab hOne divalent → e = divalent)
    (hConnected : graph_connected (contract target hab hOne))
    (hGenus : genus (contract target hab hOne) = 0)
    (endpoint : SheetPartition degree)
    (hEndVertex : data.vertexPartition (trivalentVertex hc hab hOne divalent) = endpoint)
    (hEndRefines : endpoint.Refines
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩))
    (permutation : Equiv.Perm (Fin degree))
    (hFixEnd : ∀ sheet, endpoint.Rel (permutation sheet) sheet) :
    ∃ swapped : GluingDatum target degree,
      swapped.vertexPartition a = data.vertexPartition a ∧
      swapped.vertexPartition b = data.vertexPartition b ∧
      swapped.edgePartition contracted = data.edgePartition contracted ∧
      contractDatum swapped hc hab hOne =
        W3ShiftClosure.clearData (contractDatum data hc hab hOne) direction hDirMem
          endpoint hEndRefines permutation hFixEnd ∧
      (ContractionForest data a b contracted →
        ContractionForest swapped a b contracted) ∧
      Nonempty (StableGraphIncidence.Equivalence data swapped) ∧
      ∃ swappedFD : FullDimensionalSourcePresentation swapped coordinate,
        Nonempty (Tracks swappedFD graph label) ∧
        GluingDatum.LengthMatrixPresentation.matrix swappedFD.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          swappedFD.labelling.targetEdge = fullDim.labelling.targetEdge ∧
          divalentOccurrence swapped hc hab hOne swappedFD star = divalent := by
  have hEnds := endsCompatible_of_endpointFix hc hab hOne data divalent direction
    hDivalentMem hDirMem hDirNe hOnly hConnected hGenus permutation
    (by rw [hEndVertex]; exact hFixEnd)
  refine ⟨swappedDatum data hc hab hOne _ _ permutation hEnds,
    swappedDatum_vertexPartition_left data hc hab hOne _ _ permutation hEnds,
    swappedDatum_vertexPartition_right data hc hab hOne _ _ permutation hEnds,
    swappedDatum_edgePartition_contracted data hc hab hOne _ _ permutation hEnds,
    contract_swappedDatum data hc hab hOne _ _ permutation hEnds
      (fun sheet ↦ hEndRefines.rel (hFixEnd sheet)),
    contractionForest_swappedDatum data hc hab hOne _ _ permutation hEnds,
    ⟨swappedIncidence data hc hab hOne _ _ permutation hEnds fullDim⟩,
    swappedFullDim data hc hab hOne _ _ permutation hEnds fullDim,
    ⟨sheetPresentation_tracking current (branchRelabel data hc hab hOne _ _ permutation hEnds)⟩,
    swappedFullDim_matrix data hc hab hOne _ _ permutation hEnds fullDim,
    swappedFullDim_targetEdge data hc hab hOne _ _ permutation hEnds fullDim, ?_⟩
  exact (divalentOccurrence_congr hc hab hOne data _ fullDim
    (swappedFullDim data hc hab hOne _ _ permutation hEnds fullDim) star).trans hDivalent

end Swap

section Grow

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)

include hForest hMoving

/-- **The exit for a Position II.a incoming cover.**  The incoming cover is
Figure 29's `k_α + 1` member on its own moving direction, and the partner it must
exit onto is the `k_α − 1` member, which needs Position II.b's sheet -- a sheet
of `e_α` outside `e_β ∪ e_γ` -- that the case's arithmetic does not supply
(`W3ShiftSourceCandidates.shift_arithmetic_does_not_force_shrinkSheet`).

Two DV branch swaps do supply it, and they are performed here on the **incoming**
datum, before the contraction: `W3ShiftClosure.exists_gaugeCopy_shrinkSheet_endpoint`
chooses both permutations inside blocks of the trivalent endpoint's own
partition -- whose finer arithmetic `endpoint_inputs` reads off
`W3ShiftClosure.RetainedBelow` and the census's own `selectedRight = A₀` clause --
so `W3ShiftIncomingTransport.EndsCompatible` holds and
`W3ShiftIncomingTransport.contract_swappedDatum` identifies the twice-swapped
cover's wall datum with the gauge copy the pair lives over.  Nothing a consumer
reads changes: the determinants, the metric equation and the stable incidence
graph are all against the **original** incoming cover. -/
theorem exists_tracked_exit_of_growPosition
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (hRetained : W3ShiftClosure.RetainedBelow shift)
    (hCensus : SelectedCensus data hc hab hOne star input shift.growPartition
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) shift.growPartition)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  have hConnected : graph_connected (contract target hab hOne) :=
    graph_connected_contract target hab hOne fullDim.targetConnected
  have hGenus : genus (contract target hab hOne) = 0 :=
    (genus_contract target hab hOne).trans fullDim.targetGenus
  obtain ⟨hFirstRef, hSecondRef, hFirstRel, hSecondRel, hFirstLt, hSecondLt⟩ :=
    endpoint_inputs data hc hab hOne fullDim star input shift hMoving hRetained hCensus
  have hEndRef := trivalent_refines data hc hab hOne fullDim star
  obtain ⟨permFirst, hFixFirst, permSecond, hFixSecond, gaugeInput, gaugeShift, copy,
    hSheet⟩ :=
    W3ShiftClosure.exists_gaugeCopy_shrinkSheet_endpoint input shift _ hEndRef hFirstRef
      hSecondRef hFirstRel hSecondRel hFirstLt hSecondLt hConnected hGenus
  -- the same two swaps, one level up on the incoming datum
  have hOnly := only_divalent data hc hab hOne fullDim star input shift hMoving
  have hDvMem : divalentOccurrence data hc hab hOne fullDim star ∈
      GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V) := by
    rw [← hMoving]; exact shift.movingTarget_mem
  have hNeFirst : divalentOccurrence data hc hab hOne fullDim star ≠ shift.firstTarget := by
    rw [← hMoving]; exact shift.moving_target_ne_first
  have hNeSecond : divalentOccurrence data hc hab hOne fullDim star ≠
      shift.secondTarget := by
    rw [← hMoving]; exact shift.moving_target_ne_second
  obtain ⟨dataOne, hOneA, hOneB, hOneE, hOneEq, hOneForest, ⟨incOne⟩, fdOne, ⟨trackOne⟩, hMatOne,
    hEdgeOne, hDvOne⟩ :=
    exists_tracked_incoming_swap data hc hab hOne fullDim star current _ shift.firstTarget rfl hDvMem
      shift.firstTarget_mem hNeFirst hOnly hConnected hGenus _ rfl hEndRef permFirst
      hFixFirst
  have hEndVertexOne : dataOne.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star)) =
      data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star)) := by
    unfold trivalentVertex
    cases IncomingTargetExpansion.right hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) with
    | false => simpa using hOneB
    | true => simpa using hOneA
  have hEndRefOne : (data.vertexPartition (trivalentVertex hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).Refines
      ((contractDatum dataOne hc hab hOne).vertexPartition ⟨a, hab⟩) := by
    rw [hOneEq]
    exact W3ShiftClosure.refines_clearData_wall (contractDatum data hc hab hOne)
      shift.firstTarget shift.firstTarget_mem _ hEndRef permFirst hFixFirst
  obtain ⟨dataTwo, hTwoA, hTwoB, hTwoE, hTwoEq, hTwoForest, ⟨incTwo⟩, fdTwo, ⟨trackTwo⟩, hMatTwo,
    hEdgeTwo, hDvTwo⟩ :=
    exists_tracked_incoming_swap dataOne hc hab hOne fdOne star trackOne _ shift.secondTarget hDvOne hDvMem
      shift.secondTarget_mem hNeSecond hOnly hConnected hGenus _ hEndVertexOne hEndRefOne
      permSecond hFixSecond
  -- the twice-swapped wall datum is the gauge copy the pair lives over
  have key : ∀ (D : GluingDatum (contract target hab hOne) degree)
      (_hD : contractDatum dataOne hc hab hOne = D)
      (hRefD : (data.vertexPartition (trivalentVertex hc hab hOne
          (divalentOccurrence data hc hab hOne fullDim star))).Refines
        (D.vertexPartition ⟨a, hab⟩)),
      W3ShiftClosure.clearData (contractDatum dataOne hc hab hOne) shift.secondTarget
          shift.secondTarget_mem _ hEndRefOne permSecond hFixSecond =
        W3ShiftClosure.clearData D shift.secondTarget shift.secondTarget_mem _ hRefD
          permSecond hFixSecond := by
    rintro D rfl hRefD
    rfl
  have hEqTotal : contractDatum dataTwo hc hab hOne =
      W3ShiftClosure.clearPairData shift _ hEndRef permFirst hFixFirst permSecond
        hFixSecond :=
    hTwoEq.trans (key _ hOneEq _)
  -- install the incoming cover's own transferred sheet on the gauge profile
  have hWall' : ((W3ShiftClosure.clearPairData shift _ hEndRef permFirst hFixFirst
        permSecond hFixSecond).vertexPartition ⟨a, hab⟩).Rel
      gaugeInput.distinguishedBlock.1 shift.extraSheet := by
    refine gaugeShift.movingAnchor_wall_rel.trans ?_
    rw [copy.movingAnchor, copy.wallPartition]
    exact shift.movingAnchor_wall_rel.symm.trans shift.extraSheet_wall_rel
  have hSep' : ¬((W3ShiftClosure.clearPairData shift _ hEndRef permFirst hFixFirst
        permSecond hFixSecond).edgePartition gaugeShift.movingTarget).Rel
      gaugeShift.movingAnchor shift.extraSheet := by
    rw [copy.movingTarget, copy.movingEdge, copy.movingAnchor]
    exact shift.extraSheet_separate
  have hEdgeEq : ((W3ShiftClosure.clearPairData shift _ hEndRef permFirst hFixFirst
        permSecond hFixSecond).edgePartition gaugeShift.movingTarget) =
      (contractDatum data hc hab hOne).edgePartition shift.movingTarget := by
    rw [copy.movingTarget]
    exact copy.movingEdge
  have hGrow : (gaugeShift.withExtra shift.extraSheet hWall' hSep').growPartition =
      shift.growPartition :=
    mergeBlocks_congr hEdgeEq copy.movingAnchor _ _
  obtain ⟨shrink⟩ :=
    exists_shrinkData (gaugeShift.withExtra shift.extraSheet hWall' hSep') hSheet
  -- carry the identification data to the twice-swapped wall datum
  obtain ⟨W, hEqW, inputW, shiftW, shrinkW, hMovingW, hBlockW, hClassW⟩ :
      ∃ (W : GluingDatum (contract target hab hOne) degree)
        (_hEqW : W = contractDatum dataTwo hc hab hOne)
        (inputW : W3SourceInput W star) (shiftW : ShiftProfile inputW)
        (shrinkW : ShrinkData shiftW),
        shiftW.movingTarget = divalentOccurrence dataTwo hc hab hOne fdTwo star ∧
        inputW.distinguishedBlock.1 = input.distinguishedBlock.1 ∧
        ∃ index : Fin 2, (shift.growPartition,
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩),
            shift.growPartition) = shiftClasses shrinkW index := by
    refine ⟨_, hEqTotal.symm, gaugeInput,
      gaugeShift.withExtra shift.extraSheet hWall' hSep', shrink, ?_, ?_, 1, ?_⟩
    · exact copy.movingTarget.trans (hMoving.trans hDvTwo.symm)
    · have hAnchor : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          gaugeInput.distinguishedBlock.1 shift.movingAnchor := by
        have hStep := gaugeShift.movingAnchor_wall_rel
        rw [copy.movingAnchor] at hStep
        exact rel_of_eq_partition copy.wallPartition hStep
      exact block_val_eq copy.wallPartition _ _
        (hAnchor.trans shift.movingAnchor_wall_rel.symm)
    · refine Eq.trans ?_ (W3ShiftClosureUnconditional.shiftClasses_one shrink).symm
      rw [hGrow, copy.wallPartition]
  subst hEqW
  -- the census over the twice-swapped cover
  have hCensusW : SelectedCensus dataTwo hc hab hOne star inputW shift.growPartition
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) shift.growPartition :=
    selectedCensus_transfer hc hab hOne star data dataTwo (hTwoA.trans hOneA)
      (hTwoB.trans hOneB) (hTwoE.trans hOneE) input inputW hBlockW _ _ _ hCensus
  have hEdgeD : fdTwo.labelling.targetEdge = fullDim.labelling.targetEdge :=
    hEdgeTwo.trans hEdgeOne
  have hMatD : GluingDatum.LengthMatrixPresentation.matrix fdTwo.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation :=
    hMatTwo.trans hMatOne
  obtain ⟨incoming, outgoing, hNe, hIndex, outgoingFD, ⟨hGraph⟩, hTrack, hSign, velocity, δ, hδ,
    hStep⟩ :=
    W3ShiftGraphTracking.exists_tracked_exit_in_original_coordinates dataTwo hc hab
      hOne fdTwo (hTwoForest (hOneForest hForest)) star inputW shiftW hMovingW shrinkW
      _ _ _ trackTwo hCensusW hClassW z incomingVelocity (by rw [hEdgeD]; exact hz)
      (by rw [hEdgeD]; exact hzpos) (by rw [hEdgeD]; exact hDirection)
  refine ⟨_, contractDatum dataTwo hc hab hOne, ⟨a, hab⟩, shiftMembers shrinkW outgoing,
    inputW.valid, hConnected, hGenus, outgoingFD.valid,
    ⟨(incOne.trans incTwo).trans hGraph⟩, outgoingFD, hTrack, ?_, velocity, δ, hδ, ?_⟩
  · rw [← hMatD]; exact hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by rw [← hMatD]; exact hMetric, hPencil⟩

end Grow

section Classification
variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include hForest hCompat in
/-- Actual `w3Shift` classification supplies the profile, orientation,
positional census, clearing permutations and pair. All are derived; only the
current source's Tracks invariant is supplied. -/
theorem trackedExit_of_classification
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (classification : W3IncomingClassification.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w3Shift)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  obtain ⟨profile, directions, largest_lt⟩ := exists_shift_payload classification hTag
  obtain ⟨shift, hMoving, hRetained, hCases⟩ :=
    exists_shiftProfile_census data hc hab hOne fullDim hForest hCompat star input
      profile directions largest_lt
  rcases hCases with ⟨shrink, hCensus⟩ | hCensus
  · exact W3ShiftGraphTracking.exists_tracked_exit_of_shrinkPosition data hc hab hOne fullDim hForest star
      input shift hMoving shrink current hCensus z incomingVelocity hz hzpos hDirection
  · exact exists_tracked_exit_of_growPosition data hc hab hOne fullDim hForest star
      input shift hMoving current hRetained hCensus z incomingVelocity hz hzpos hDirection


end Classification
end DraismaVargas.LocalCases.W3ShiftTrackedFinal
