import DraismaVargas.LocalCases.InteriorProgress
import DraismaVargas.LocalCases.W3ShiftTrackedFinal
import DraismaVargas.LocalCases.W3TrackedCensus

/-!
# The two trivalent tag bridges of `InteriorProgress`: `w3Shift` and `w3Four`

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6: Case
`{w3-r1-nd3-t2-(a>k4)}` (Figure 29 and Equation (3), the `w3Shift` pair) and
Case `{w3-r1-nd3-t2-(a=k4)}` (Figure 28 and Equation (2), the `w3Four`
family); read against Vargas, Part II (arXiv:2609.09109), Section 4 (the
wall-crossing proposition, and the proof of the main theorem, which walks a
generic path across codimension-one walls), and the per-tag obligations
`InteriorProgress.W3Bridge` / `W2Bridge` / `WallBridge`.

`DraismaVargas/LocalCases/InteriorProgress.lean` discharges six of the ten
per-tag bridges (`w4`, `w3Nd2CoarseFine`, `w3Nd3CoarseFine`, `w2M11`, `w2P`,
`w2R1`) and keeps `w3Four`, `w3Shift`, `w2M1k`, `w2Mkk` as hypotheses.  The two
bridges below are `InteriorProgress.W3Bridge` at its two trivalent tags, and
the corollary is `InteriorProgress.wallBridge_of_remaining` with them
supplied.

## What is proved here

### 1.  `w3Bridge_shift : InteriorProgress.W3Bridge … SourceCase.w3Shift`

`TrackedWallProgress.trackedW3Shift` wants Figure 29's `ShrinkData`, a member
index, a full-dimensional presentation of that member, the family's regrown
column and one `InteriorGraphTracking.Tracks` at that presentation.  The
`w3Shift` constructor of `W3IncomingClassification.Classification` supplies only
an `Nd3Profile`, the distinct directions and the largest-index bound.

`exists_shift_matched_tracking_of_classification` supplies the rest.  It
re-runs the *first half* of `W3ShiftTrackedFinal.trackedExit_of_classification`,
which assembles all of this internally before handing it to the exit:

* `W3ShiftClosureFinal.exists_shift_payload` and `exists_shiftProfile_census`
  produce the `ShiftProfile`, the moving-target identity
  `shift.movingTarget = divalentOccurrence …` and the Position II.b / II.a
  dichotomy of `W3ShiftIncomingMatching.SelectedCensus`es;
* in Position II.b the `ShrinkData` comes with the census and the dichotomy is
  `W3ShiftClosureUnconditional.dichotomy_zero`;
* in Position II.a the two DV branch swaps are performed one level up on the
  **incoming** datum (`W3ShiftTrackedFinal.exists_tracked_incoming_swap`), the
  twice-swapped wall datum is identified with
  `W3ShiftClosure.clearPairData` and the incoming cover's own transferred sheet
  is installed on the gauge profile, which is where the `ShrinkData` comes from
  (`W3ShiftSourceCandidates.exists_shrinkData`);
* either way `W3ShiftGraphTracking.exists_matched_tracking` identifies the
  incoming cover as a **named member** `shiftMembers shrink index` carrying its
  own honest presentation, the matrix identity against the incoming cover and
  hence a `Tracks`.

The returned wall datum is the incoming cover's own contracted datum in Position
II.b and the twice-swapped copy of it in Position II.a; `TrackedRoutedWall` does
not mention it, so the bridge is uniform.  `A04ShiftWiring.shiftRows_wallColumn`
turns the matched tracking's column clause into
`(shiftRows …).wallColumn = column`, the hypothesis `trackedW3Shift` takes.

### 2.  `w3Bridge_four : InteriorProgress.W3Bridge … SourceCase.w3Four`

`TrackedWallProgressMore.trackedW3Four` wants
`W3FourRegrownColumnSeam.MemberCertificates` (Figure 28's four honest receipts
with their four dictionaries and four source-genus receipts),
`W3TrackedAnchoring.RowsCompatible` at a stable path labelling of the wall
datum, a member index with a full-dimensional presentation, the regrown column
and one `Tracks`.

`exists_four_matched_tracking_of_classification` produces all of them from the
`four` constructor alone.  **No input is missing**: the `PositionPlan` and the
root receipts `W3TrackedAnchoring.exists_tracked_anchoredCertificates_withExtra`
asks for are *derived*, not supplied ---

* the extra sheets and the `PositionPlan` come from the incoming cover's own
  census (`W3TrackedCensus.exists_tracked_censusAnchoring`, which branches on
  `W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest` and
  picks `W3FourClosureFinal.somePositionPlan` or the literal Position I/II.b
  shape `W3FourSelectedCensus.classes_of_largest` names), and it returns
  `NaturalRowsCompatible`, whence `RowsCompatible` by
  `W3TrackedAnchoring.rowsCompatible_of_natural`;
* the root is `TargetSeparation.farEndpoint ⟨a, hab⟩ t₃`, and its three
  `TargetBranchRegion.edgeMoved` receipts are
  `TargetSeparation.edgeMoved_eq_false` twice and
  `edgeMoved_self_eq_true` once, from the wall's own connectedness and genus
  zero and the three directions' distinctness.

The identified incoming member is then
`W3InteriorGraphTracking.exists_matched_tracking` against
`W3FourIncomingMatching.figure28MembersWithExtra`, moved onto Equation (2)'s own
four members by `W3TrackedExit.exists_family_matched_tracking` (literal
candidate equalities, not matrix equalities), and its column clause is
`W3FourHonestReceipts.wallColumn` by definitional unfolding.

### 3.  `wallBridge_of_divalent`

`InteriorProgress.wallBridge_of_remaining` with the two trivalent tags
supplied: the wall bridge at one chart from the two **divalent** tags `w2M1k`
and `w2Mkk` alone.  Composed with `InteriorProgress.trackedClassified_of_state`
and `interior_of_bridges`, this reduces the `interior` hypothesis of
`OuterWalk.coneEntry_of_reaches` to those two tags, the march's three metric
facts and the genericity hypothesis `SimpleNegativeCrossings`.

## Hypotheses left explicit here

* The two **divalent** tags `w2M1k` and `w2Mkk`, as `W2Bridge` hypotheses of
  `wallBridge_of_divalent`; `InteriorBridgesDivalent` discharges them and
  `InteriorBridgesAll` combines the two files.  Each has two bases (an
  orientation the classification does not name), and its
  `exists_matched_tracking` is stated on the members of
  `W2M1kIncomingMatching` / `W2MkkIncomingMatching` rather than on the
  `A04M1kWiring` / `A04MoreTags` family slots.
* The march's three metric facts (`0 < baseStart`, `0 ≤ baseFinish`,
  `0 ≤ restartTime`), which give the interior wall metric at the coordinate the
  march crosses; see `InteriorProgress`' module header.
* The genericity hypothesis `SimpleNegativeCrossings` at every state.

Nothing here identifies a graph by a matrix: every tracking travels along the
actual `StableGraphIncidence.Equivalence` the matched-tracking producers
return, and every candidate cast is a literal candidate equality.
`InteriorProgress`, `TrackedWallProgress`, `TrackedWallProgressMore`,
`A04ShiftWiring`, `W3ShiftTrackedFinal`, `W3TrackedCensus`, `W3TrackedExit` and
`W3ShiftGraphTracking` are used as they stand.

Consumers: `InteriorProgress.wallBridge_of_tagBridges` /
`wallBridge_of_remaining`, hence `InteriorProgress.trackedClassified_of_state`,
`interior_of_bridges` and `OuterWalk.coneEntry_of_reaches` behind them.
-/

namespace DraismaVargas.LocalCases.InteriorBridgesTrivalent

noncomputable section

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open GraphContraction GluingContraction ContractionRamification ContractionFibre
open TargetExpansion WallDegeneration
open W4Assembly W4StableSource ThirdEquation W3R1SourceProfile FullDimensionalSource
open InteriorGraphTracking
open InteriorProgress
open ClassifiedContinuation (SourceCase)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {chart : Matrix coordinate coordinate ℚ}
  {graph : CubicDartGraph D V} {label : D → coordinate}

/-! ## 1.  Figure 29, the `w3Shift` tag -/

section Shift

open W3ShiftSourceCandidates W3ShiftIncomingMatching W3ShiftIncomingTransport
open W3ShiftClosureFinal
open W3ShiftLimitRows (shiftMembers)
open W3ShiftTrackedFinal (exists_tracked_incoming_swap)
open W3Nd2IncomingTargetPlacement (divalentOccurrence)

/-- **Figure 29's identified incoming member, exposed from the classification.**

The first half of `W3ShiftTrackedFinal.trackedExit_of_classification`, stopped
one step before the exit: from the `w3Shift` tag alone it returns the wall datum
Equation (3)'s pair lives over (the incoming cover's own contracted datum in
Position II.b, its twice-branch-swapped copy in Position II.a), that datum's
`W3SourceInput`, the `ShiftProfile` and its `ShrinkData`, the index of the
member the incoming cover **is**, that member's own full-dimensional
presentation, the matrix identity against the incoming cover, the regrown-column
identity in `A04ShiftWiring.shiftRows`' own shape, and the transported
`Tracks`.  The contraction forest and the dangling compatibility are the only
wall inputs, and `InteriorProgress` derives both from the wall metric. -/
theorem exists_shift_matched_tracking_of_classification
    {target : CFGraph.{0}} {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (current : Tracks fullDim graph label)
    (classification : W3IncomingClassification.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = SourceCase.w3Shift) :
    ∃ (wallDatum : GluingDatum (contract target hab hOne) degree)
      (wallInput : W3SourceInput wallDatum star) (shift : ShiftProfile wallInput)
      (shrink : ShrinkData shift) (index : Fin 2)
      (fd : FullDimensionalSourcePresentation (shiftMembers shrink index).datum coordinate),
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
        (A04ShiftWiring.shiftRows shrink wallInput.valid index fd).wallColumn =
          fullDim.labelling.targetEdge.symm contracted ∧
        Nonempty (Tracks fd graph label) := by
  classical
  obtain ⟨profile, directions, largest_lt⟩ := exists_shift_payload classification hTag
  obtain ⟨shift, hMoving, hRetained, hCases⟩ :=
    exists_shiftProfile_census data hc hab hOne fullDim hForest hCompat star input
      profile directions largest_lt
  rcases hCases with ⟨shrink, hCensus⟩ | hCensus
  · obtain ⟨index, -, fd, hMatrix, hWall, -, -, hTrack⟩ :=
      W3ShiftGraphTracking.exists_matched_tracking data hc hab hOne fullDim hForest star input
        shift hMoving shrink _ _ _ current hCensus
        (W3ShiftClosureUnconditional.dichotomy_zero shrink)
    exact ⟨_, input, shift, shrink, index, fd, hMatrix,
      (A04ShiftWiring.shiftRows_wallColumn shrink input.valid index fd).trans hWall, hTrack⟩
  · have hConnected : graph_connected (contract target hab hOne) :=
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
    have hOnly := only_divalent data hc hab hOne fullDim star input shift hMoving
    have hDvMem : divalentOccurrence data hc hab hOne fullDim star ∈
        GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V) := by
      rw [← hMoving]; exact shift.movingTarget_mem
    have hNeFirst : divalentOccurrence data hc hab hOne fullDim star ≠ shift.firstTarget := by
      rw [← hMoving]; exact shift.moving_target_ne_first
    have hNeSecond : divalentOccurrence data hc hab hOne fullDim star ≠
        shift.secondTarget := by
      rw [← hMoving]; exact shift.moving_target_ne_second
    obtain ⟨dataOne, hOneA, hOneB, hOneE, hOneEq, hOneForest, ⟨incOne⟩, fdOne, ⟨trackOne⟩,
      hMatOne, hEdgeOne, hDvOne⟩ :=
      exists_tracked_incoming_swap data hc hab hOne fullDim star current _ shift.firstTarget rfl
        hDvMem shift.firstTarget_mem hNeFirst hOnly hConnected hGenus _ rfl hEndRef permFirst
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
    obtain ⟨dataTwo, hTwoA, hTwoB, hTwoE, hTwoEq, hTwoForest, ⟨incTwo⟩, fdTwo, ⟨trackTwo⟩,
      hMatTwo, hEdgeTwo, hDvTwo⟩ :=
      exists_tracked_incoming_swap dataOne hc hab hOne fdOne star trackOne _ shift.secondTarget
        hDvOne hDvMem shift.secondTarget_mem hNeSecond hOnly hConnected hGenus _ hEndVertexOne
        hEndRefOne permSecond hFixSecond
    have key : ∀ (E : GluingDatum (contract target hab hOne) degree)
        (_hE : contractDatum dataOne hc hab hOne = E)
        (hRefE : (data.vertexPartition (trivalentVertex hc hab hOne
            (divalentOccurrence data hc hab hOne fullDim star))).Refines
          (E.vertexPartition ⟨a, hab⟩)),
        W3ShiftClosure.clearData (contractDatum dataOne hc hab hOne) shift.secondTarget
            shift.secondTarget_mem _ hEndRefOne permSecond hFixSecond =
          W3ShiftClosure.clearData E shift.secondTarget shift.secondTarget_mem _ hRefE
            permSecond hFixSecond := by
      rintro E rfl hRefE
      rfl
    have hEqTotal : contractDatum dataTwo hc hab hOne =
        W3ShiftClosure.clearPairData shift _ hEndRef permFirst hFixFirst permSecond
          hFixSecond :=
      hTwoEq.trans (key _ hOneEq _)
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
    have hCensusW : SelectedCensus dataTwo hc hab hOne star inputW shift.growPartition
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) shift.growPartition :=
      selectedCensus_transfer hc hab hOne star data dataTwo (hTwoA.trans hOneA)
        (hTwoB.trans hOneB) (hTwoE.trans hOneE) input inputW hBlockW _ _ _ hCensus
    have hEdgeD : fdTwo.labelling.targetEdge = fullDim.labelling.targetEdge :=
      hEdgeTwo.trans hEdgeOne
    have hMatD : GluingDatum.LengthMatrixPresentation.matrix fdTwo.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation :=
      hMatTwo.trans hMatOne
    obtain ⟨index, -, fd, hMatrix, hWall, -, -, hTrack⟩ :=
      W3ShiftGraphTracking.exists_matched_tracking dataTwo hc hab hOne fdTwo
        (hTwoForest (hOneForest hForest)) star inputW shiftW hMovingW shrinkW _ _ _ trackTwo
        hCensusW hClassW
    refine ⟨_, inputW, shiftW, shrinkW, index, fd, hMatrix.trans hMatD, ?_, hTrack⟩
    refine (A04ShiftWiring.shiftRows_wallColumn shrinkW inputW.valid index fd).trans ?_
    rw [hWall, hEdgeD]

/-- **Figure 29, the `w3Shift` tag, discharged.**  The same three steps as the
six bridges of `InteriorProgress`: the payload extractor (here the whole of
`exists_shift_matched_tracking_of_classification`), the matched tracking, and
the family's regrown-column identity; then `TrackedWallProgress.trackedW3Shift`.
`hValid` is the identified wall datum's own `W3SourceInput.valid`, so no
validity receipt is carried. -/
theorem w3Bridge_shift : W3Bridge degree coordinate chart graph label SourceCase.w3Shift := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  obtain ⟨wallDatum, wallInput, shift, shrink, index, fd, hMatrix, hWall, ⟨trackFd⟩⟩ :=
    exists_shift_matched_tracking_of_classification data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest hCompat star
      input tracks classification hTag
  exact ⟨TrackedWallProgress.trackedW3Shift (wall := column) shrink wallInput.valid
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    index fd (hWall.trans (targetEdge_symm_contractedEdge fullDim column))
    ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩

end Shift

/-! ## 2.  Figure 28, the `w3Four` tag -/

section Four

open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSourceCandidates (growProfileFirst)
open W3FourRegrownColumnSeam (MemberCertificates)
open W3TrackedAnchoring (RowsCompatible rowsCompatible_of_natural)
open W3FourIncomingMatching (figure28MembersWithExtra figure28MembersWithExtra_dichotomy)
open W3TrackedExit (exists_family_matched_tracking)
open W3FourHonestReceipts (wallColumn)

/-- **Figure 28's certified members and identified incoming member, exposed from
the classification.**

Stopped before the member exit, this returns, from the `w3Four` tag alone,
Equation
(2)'s four-star geometry, the `MemberCertificates` bundle (four honest receipts,
four dictionaries, four source-genus receipts), the wall datum's stable path
labelling with `W3TrackedAnchoring.RowsCompatible` at it, the index of the
member the incoming cover **is**, that member's own full-dimensional
presentation, the matrix identity, the regrown column in
`W3FourHonestReceipts.wallColumn`'s shape and the transported `Tracks`.

Every input `W3TrackedAnchoring.exists_tracked_anchoredCertificates_withExtra`
asks for beyond the classification is derived here: the two extra sheets and the
`PositionPlan` inside `W3TrackedCensus.exists_tracked_censusAnchoring`, and the
root with its three `TargetBranchRegion.edgeMoved` receipts from
`TargetSeparation.farEndpoint` at `t₃` together with the wall's connectedness
and genus zero. -/
theorem exists_four_matched_tracking_of_classification
    {target : CFGraph.{0}} {a b : target.V} {contracted : target.edges}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (current : Tracks fullDim graph label)
    (classification : W3IncomingClassification.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = SourceCase.w3Four) :
    ∃ (geometry : FourStarGeometry (contractDatum data hc hab hOne) ⟨a, hab⟩)
      (certified : MemberCertificates (contractDatum data hc hab hOne) ⟨a, hab⟩ geometry)
      (wallLabelling : StablePathLabelling (contractDatum data hc hab hOne))
      (incoming : Fin 4)
      (incomingFD : FullDimensionalSourcePresentation
        (certified.receipts.candidate incoming).datum coordinate),
      RowsCompatible certified wallLabelling ∧
        GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
        wallColumn certified incoming incomingFD.labelling =
          fullDim.labelling.targetEdge.symm contracted ∧
        Nonempty (Tracks incomingFD graph label) := by
  classical
  cases classification with
  | shift => cases hTag
  | nd3CoarseFine => cases hTag
  | nd2CoarseFine => cases hTag
  | four profile directions largest_index _pair_index =>
    have hConnected : graph_connected (contract target hab hOne) :=
      graph_connected_contract target hab hOne fullDim.targetConnected
    have hGenus : genus (contract target hab hOne) = 0 :=
      (genus_contract target hab hOne).trans fullDim.targetGenus
    have hOtherIncident :
        (((growProfileFirst profile directions largest_index).otherTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).1 = ⟨a, hab⟩ ∨
          (((growProfileFirst profile directions largest_index).otherTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).2 = ⟨a, hab⟩ :=
      (mem_incidentEdges_iff _ _).mp
        (growProfileFirst profile directions largest_index).otherTarget_mem
    have hGrowIncident :
        (((growProfileFirst profile directions largest_index).growTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).1 = ⟨a, hab⟩ ∨
          (((growProfileFirst profile directions largest_index).growTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).2 = ⟨a, hab⟩ :=
      (mem_incidentEdges_iff _ _).mp
        (growProfileFirst profile directions largest_index).growTarget_mem
    have hLargestIncident :
        (((growProfileFirst profile directions largest_index).largestTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).1 = ⟨a, hab⟩ ∨
          (((growProfileFirst profile directions largest_index).largestTarget :
            (contract target hab hOne).edges) :
              (contract target hab hOne).V × (contract target hab hOne).V).2 = ⟨a, hab⟩ :=
      (mem_incidentEdges_iff _ _).mp
        (growProfileFirst profile directions largest_index).largestTarget_mem
    have hTreeRoot : TargetSeparation.farEndpoint (⟨a, hab⟩ : (contract target hab hOne).V)
        (growProfileFirst profile directions largest_index).otherTarget ≠ ⟨a, hab⟩ :=
      TargetSeparation.farEndpoint_ne hOtherIncident
    have hGrowFixed : TargetBranchRegion.edgeMoved
        (⟨a, hab⟩ : (contract target hab hOne).V) _ hTreeRoot
        (growProfileFirst profile directions largest_index).growTarget = false :=
      TargetSeparation.edgeMoved_eq_false hConnected hGenus hOtherIncident hGrowIncident
        (Ne.symm (growProfileFirst profile directions largest_index).grow_target_ne_other)
    have hLargestFixed : TargetBranchRegion.edgeMoved
        (⟨a, hab⟩ : (contract target hab hOne).V) _ hTreeRoot
        (growProfileFirst profile directions largest_index).largestTarget = false :=
      TargetSeparation.edgeMoved_eq_false hConnected hGenus hOtherIncident hLargestIncident
        (growProfileFirst profile directions largest_index).other_target_ne_largest
    have hOtherMoved : TargetBranchRegion.edgeMoved
        (⟨a, hab⟩ : (contract target hab hOne).V) _ hTreeRoot
        (growProfileFirst profile directions largest_index).otherTarget = true :=
      TargetSeparation.edgeMoved_self_eq_true hOtherIncident
    obtain ⟨anchoring, hRows⟩ :=
      W3TrackedCensus.exists_tracked_censusAnchoring data hc hab hOne fullDim hForest hCompat
        star input profile directions largest_index _ hTreeRoot hGrowFixed hLargestFixed
        hOtherMoved
    have hDichotomy := figure28MembersWithExtra_dichotomy data hc hab hOne fullDim hForest
      hCompat star input profile directions largest_index anchoring.extraFirst
      anchoring.extraFirst_wall anchoring.extraFirst_separate anchoring.extraSecond
      anchoring.extraSecond_wall anchoring.extraSecond_separate
      anchoring.anchored.positionMember anchoring.anchored.positionMember_isolated
    obtain ⟨index, -, matched, hMatrix, hWall, -, -, ⟨hTrack⟩⟩ :=
      W3InteriorGraphTracking.exists_matched_tracking data fullDim current hc hab hOne hForest
        star input (figure28MembersWithExtra profile directions largest_index
          anchoring.extraFirst anchoring.extraFirst_wall anchoring.extraFirst_separate
          anchoring.extraSecond anchoring.extraSecond_wall anchoring.extraSecond_separate
          anchoring.anchored.positionMember) hDichotomy anchoring.census
    obtain ⟨incoming, incomingFD, hIncomingMatrix, hIncomingWall, hIncomingTrack⟩ :=
      exists_family_matched_tracking input profile directions largest_index
        anchoring.extraFirst anchoring.extraFirst_wall anchoring.extraFirst_separate
        anchoring.extraSecond anchoring.extraSecond_wall anchoring.extraSecond_separate
        anchoring.positionPlan anchoring.anchored index matched hTrack
    refine ⟨_, anchoring.anchored.certified, _, incoming, incomingFD,
      rowsCompatible_of_natural _ _ hRows, hIncomingMatrix.trans hMatrix, ?_, hIncomingTrack⟩
    simpa only [W3FourHonestReceipts.wallColumn, W3FourHonestReceipts.targetCoordinates,
      Equiv.symm_trans_apply, Equiv.symm_symm] using hIncomingWall.trans hWall

/-- **Figure 28, the `w3Four` tag, discharged.**
`TrackedWallProgressMore.trackedW3Four`, the producer that presents Equation (2)
at the identified member's own coordinates, so the only equations it takes are
the state--classifier chart
identity and the regrown column.  `hValid` is `input.valid`; the four
dictionaries and the four source-genus receipts are `MemberCertificates`' own
fields. -/
theorem w3Bridge_four : W3Bridge degree coordinate chart graph label SourceCase.w3Four := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data
    (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column) hForest
  obtain ⟨geometry, certified, wallLabelling, incoming, incomingFD, hCompatRows, hMatrix,
    hWall, ⟨trackFd⟩⟩ :=
    exists_four_matched_tracking_of_classification data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest hCompat star
      input tracks classification hTag
  exact ⟨TrackedWallProgressMore.trackedW3Four (wall := column) certified input.valid
    (graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected)
    ((genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus)
    incoming incomingFD wallLabelling hCompatRows
    (hWall.trans (targetEdge_symm_contractedEdge fullDim column))
    ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩

end Four

/-! ## 3.  The wall bridge at one chart from the two divalent tags -/

section Divalent

/-- **The wall bridge at one chart, from the two divalent tags.**
`InteriorProgress.wallBridge_of_remaining` with its two trivalent hypotheses
supplied by this file: of the ten per-tag bridges only `w2M1k` and `w2Mkk`
remain as hypotheses.  Composed with `InteriorProgress.trackedClassified_of_state`
and `InteriorProgress.interior_of_bridges`, this reduces the `interior`
hypothesis of `OuterWalk.coneEntry_of_reaches` to those two tags, the march's
three metric facts and the genericity hypothesis `SimpleNegativeCrossings`. -/
theorem wallBridge_of_divalent
    (b2M1k : W2Bridge degree coordinate chart graph label SourceCase.w2M1k)
    (b2Mkk : W2Bridge degree coordinate chart graph label SourceCase.w2Mkk) :
    WallBridge degree coordinate chart graph label :=
  wallBridge_of_remaining w3Bridge_four w3Bridge_shift b2M1k b2Mkk

end Divalent

end

end DraismaVargas.LocalCases.InteriorBridgesTrivalent
