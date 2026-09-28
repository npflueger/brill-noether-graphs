import DraismaVargas.LocalCases.InteriorProgress

/-!
# The two divalent interior bridges: Figure 33 (`w2M1k`) and Figure 34 (`w2Mkk`)

Source: Vargas, Part II, the subsections *Wall crossing* and *Proofs of the
main theorems* (the cone marches of the outer walk), read against the cases of
Draisma--Vargas Part I

* `{w2-r2-nd3-M-1k}` -- Figure 33 and Equation (7), with the factor of two in
  the second bracket of Equation (7) explained in `W2M1kCommonBalance`; and
* `{w2-r2-nd3-M-kk}` -- Figure 34 and Equation (8).

`InteriorProgress` states the per-tag obligations `W4Bridge`, `W3Bridge tag`,
`W2Bridge tag`, dispatches the ten-way interior classification over them
(`wallBridge_of_tagBridges`) and discharges six of the ten tags, leaving four:
`w3Four`, `w3Shift`, `w2M1k` and `w2Mkk`.  This file discharges the two
**divalent** ones.

## What is proved here

`w2Bridge_m1k : W2Bridge … SourceCase.w2M1k` and
`w2Bridge_mkk : W2Bridge … SourceCase.w2Mkk`: at every cover displaying the
chart, with its `InteriorGraphTracking.Tracks`, at a coordinate carrying an
`InteriorProgress.AdmissibleColumn` wall metric, and with the classification's
own two-star, wall input and `w2M1k`/`w2Mkk`-tagged
`IncomingSourceCases.W2.Classification`, that coordinate's
`TrackedWallProgress.TrackedRoutedWall`.

Each is the three steps of `InteriorProgress.w2Bridge_r1`:

1. **Payload.** `W2M1kGraphTracking.exists_w2M1k_payload` /
   `W2MkkGraphTracking.exists_w2Mkk_payload` reads the wall block, the
   `W2R2SourceProfile.SourceProfile` and the M-1k / M-kk `Shape` (and, for
   `w2Mkk`, the `r = 0` background) out of the classification's constructor.
2. **Orientation and identification.**  The bases the producers want are named
   by the *datum*, not by the classification: for Figure 33 by
   `W2M1kClosureUnconditional.headline_cases` (leaf endpoint, or an aligned or a
   separated divalent datum), for Figure 34 by
   `W2MkkSourceCandidates.exists_firstMember_or_secondMember`.  Then
   `exists_matched_tracking` identifies the incoming cover as a named member
   carrying its own honest presentation in the original coordinates, its
   stable-incidence certificate, and hence an `InteriorGraphTracking.Tracks` at
   that member.  Figure 33's three census inputs
   (`W2M1kSelectedCensus.exists_selectedCensus_leaf`,
   `selectedCensus_of_aligned`, `selectedCensus_dichotomy_of_dividedData`) and
   Figure 34's (`W2MkkSelectedCensus.divalent_endpoints`,
   `selectedCensus_dichotomy`) are produced, never assumed; the contraction
   forest is derived from the wall metric inside each bridge, so no receipt is
   carried.
3. **Production.** `TrackedWallProgressMore.trackedW2M1kAligned` /
   `trackedW2M1kSeparated` / `trackedW2MkkFirst` / `trackedW2MkkSecond` apply at
   the identified `Fin 3` slot, with `hwallColumn` supplied by the family's own
   regrown-column identity (`A04M1kWiring.m1kAlignedFamily_wallColumn`,
   `m1kSeparatedFamily_wallColumn`, `A04MoreTags.mkkFirstFamily_wallColumn`,
   `mkkSecondFamily_wallColumn`) composed with the matched tracking's column
   identity and `InteriorProgress.targetEdge_symm_contractedEdge`.

The slot dictionary is as follows: Figure 33 puts the leaf member at
aligned position `0`, the joined member `M⁽³⁾` at aligned position `2`, the
divided member `M⁽²⁾` at separated position `1` and the joined member at
separated position `2`; Figure 34's two-element
`W2MkkIncomingMatching.members` index goes to first positions `0`, `2` and to
second positions `1`, `2`.  No family-slot identity needs to be proved: the
family slots of the routed walls (`A04M1kWiring`, `A04MoreTags`) and the
incoming-matching members are the *same* terms --
`W2M1kLimitColumns.localLeafMember`, `localDividedMember` and `joinedMember`
define their `right` and `datum` fields to be exactly
`LeafPair.candidate`'s, `DividedData.candidate`'s and `joinedCandidate`'s, and
the orientations' `member` fields are `Matrix.cons` literals -- so the routed
wall's family slot presents the incoming-matching member definitionally and the
regrown-column identities compose with `Eq.trans` alone.

`wallBridge_of_trivalent` is the corollary: with these two, the wall bridge at
one chart (`InteriorProgress.WallBridge`) follows from the two **trivalent**
tags `w3Four` and `w3Shift` alone, through
`InteriorProgress.wallBridge_of_remaining`.

## The hypotheses that remain explicit here

* The two trivalent bridges `W3Bridge … w3Four` and `W3Bridge … w3Shift`, which
  `wallBridge_of_trivalent` takes as hypotheses; `InteriorBridgesTrivalent`
  proves them (`w3Bridge_four`, `w3Bridge_shift`).  As `InteriorProgress`'s
  header records, `w3Four` needs `W3TrackedAnchoring.RowsCompatible` and
  `W3FourRegrownColumnSeam.MemberCertificates` at the reached wall, and
  `w3Shift` the shift profile's `ShrinkData`, its three selected sheet classes
  with their `W3ShiftIncomingMatching.SelectedCensus` and the moving-target
  identity.
* The march's three metric facts (`0 < baseStart`, `0 ≤ baseFinish`,
  `0 ≤ restartTime`), which supply the interior wall metric at the crossed
  coordinate, and the genericity condition `SimpleNegativeCrossings`.  This
  file does not touch either.

Nothing here identifies a graph by a matrix: every tracking travels along the
actual `StableGraphIncidence.Equivalence` that `exists_matched_tracking`
returns.  `InteriorProgress`, `TrackedWallProgressMore`, `A04M1kWiring`,
`A04MoreTags`, `W2M1kGraphTracking` and `W2MkkGraphTracking` are used as they
stand.

Used by: `InteriorProgress.trackedClassified_of_state`,
`InteriorProgress.interior_of_bridges` and, behind them,
`OuterWalk.coneEntry_of_reaches`.
-/

namespace DraismaVargas.LocalCases.InteriorBridgesDivalent

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases.InteriorProgress
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)

variable {degree : ℕ} {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {chart : Matrix coordinate coordinate ℚ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **Figure 33, the `w2M1k` tag, discharged.**  `W2M1kGraphTracking.exists_w2M1k_payload`
rebuilds the wall block, the source profile and the M-1k `Shape` from the `m1k`
constructor's `unit_large` disjunction;
`W2M1kClosureUnconditional.headline_cases` names the orientation the datum
itself decides (Base I.a at a leaf endpoint or an aligned divalent datum, Base
II.2.2.M at a separated one); `W2M1kGraphTracking.exists_matched_tracking`
identifies the incoming cover as that base's named member with its honest
presentation and hence with a tracking; and
`A04M1kWiring.m1kAlignedFamily_wallColumn` / `m1kSeparatedFamily_wallColumn`
say that member's regrown column is the crossed coordinate.  The selected-class
censuses are produced, not assumed, and the contraction forest is derived from
the wall metric. -/
theorem w2Bridge_m1k : W2Bridge degree coordinate chart graph label SourceCase.w2M1k := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hConn : graph_connected (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) :=
    graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected
  have hGen : genus (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) = 0 :=
    (genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus
  obtain ⟨wallBlock, wallProfile, ⟨wallShape⟩⟩ :=
    W2M1kGraphTracking.exists_w2M1k_payload data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) star input classification hTag
  rcases W2M1kClosureUnconditional.headline_cases data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) fullDim wallProfile
      wallShape with
    ⟨-, hLeaf⟩ | ⟨⟨pair⟩, hLeftCard, hRightCard⟩ | ⟨⟨divided⟩, hLeftCard, hRightCard⟩
  · obtain ⟨pair, selected⟩ := W2M1kSelectedCensus.exists_selectedCensus_leaf data
      (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
      fullDim wallProfile wallShape hLeaf
    obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.leaf_sameBlocks data
      (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
      fullDim input wallProfile wallShape pair hLeaf selected
      (W2M1kLeafBackground.leafBackgroundCensus data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest input
        wallProfile hLeaf)
    obtain ⟨fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
      W2M1kGraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim
        (W2M1kSourceCandidates.LeafPair.candidate input wallShape pair)
        (W2M1kIncomingMatching.leafPlacement data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) input wallProfile wallShape
          pair hLeaf)
        hVertices hEdges tracks
    exact ⟨TrackedWallProgressMore.trackedW2M1kAligned (wall := column) input wallShape pair
      hConn hGen 0 fd
      ((A04M1kWiring.m1kAlignedFamily_wallColumn input wallShape pair hConn hGen 0 fd).trans
        (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
      ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
  · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks data
      (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
      fullDim hForest input wallProfile
      (W2M1kClosureUnconditional.wall_background data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) input wallProfile)
      hLeftCard hRightCard (pair.geometry wallShape)
      (W2M1kSelectedCensus.selectedCensus_of_aligned data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest wallProfile
        wallShape pair.aligned hLeftCard hRightCard)
    obtain ⟨fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
      W2M1kGraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim
        (W2M1kSourceCandidates.joinedCandidate star (pair.geometry wallShape))
        (W2M1kIncomingMatching.joinedPlacement data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) (pair.geometry wallShape)
          hLeftCard hRightCard)
        hVertices hEdges tracks
    exact ⟨TrackedWallProgressMore.trackedW2M1kAligned (wall := column) input wallShape pair
      hConn hGen 2 fd
      ((A04M1kWiring.m1kAlignedFamily_wallColumn input wallShape pair hConn hGen 2 fd).trans
        (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
      ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
  · have hBackground := W2M1kClosureUnconditional.wall_background data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) input wallProfile
    rcases W2M1kSelectedCensus.selectedCensus_dichotomy_of_dividedData data
        (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
        fullDim hForest wallProfile wallShape divided hLeftCard hRightCard with
      selected | selected
    · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.divided_sameBlocks data
        (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
        fullDim hForest input wallProfile hBackground hLeftCard hRightCard wallShape divided
        selected
      obtain ⟨fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
        W2M1kGraphTracking.exists_matched_tracking data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim
          (W2M1kSourceCandidates.DividedData.candidate wallShape divided)
          (W2M1kIncomingMatching.dividedPlacement data (hc_column fullDim column)
            (hab_column fullDim column) (hOne_column fullDim column) wallProfile wallShape
            divided hLeftCard hRightCard)
          hVertices hEdges tracks
      exact ⟨TrackedWallProgressMore.trackedW2M1kSeparated (wall := column) input wallShape
        divided hConn hGen 1 fd
        ((A04M1kWiring.m1kSeparatedFamily_wallColumn input wallShape divided hConn hGen 1
          fd).trans (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
    · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks data
        (hc_column fullDim column) (hab_column fullDim column) (hOne_column fullDim column)
        fullDim hForest input wallProfile hBackground hLeftCard hRightCard
        (divided.geometry wallShape) selected
      obtain ⟨fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
        W2M1kGraphTracking.exists_matched_tracking data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim
          (W2M1kSourceCandidates.joinedCandidate star (divided.geometry wallShape))
          (W2M1kIncomingMatching.joinedPlacement data (hc_column fullDim column)
            (hab_column fullDim column) (hOne_column fullDim column)
            (divided.geometry wallShape) hLeftCard hRightCard)
          hVertices hEdges tracks
      exact ⟨TrackedWallProgressMore.trackedW2M1kSeparated (wall := column) input wallShape
        divided hConn hGen 2 fd
        ((A04M1kWiring.m1kSeparatedFamily_wallColumn input wallShape divided hConn hGen 2
          fd).trans (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩

/-- **Figure 34, the `w2Mkk` tag, discharged.**  The same three steps, with
`W2MkkGraphTracking.exists_w2Mkk_payload` (which also hands over the `r = 0`
background census), `W2MkkSourceCandidates.exists_firstMember_or_secondMember`
for the orientation, `W2MkkSelectedCensus.divalent_endpoints` for the two
restored endpoints' valencies and `selectedCensus_dichotomy` for the
`DetachCensus ∨ JoinedCensus` that `W2MkkGraphTracking.exists_matched_tracking`
takes, and `A04MoreTags.mkkFirstFamily_wallColumn` /
`mkkSecondFamily_wallColumn` for the regrown column.  The distinguished sheet of
`M⁽³⁾` is the profile's own pinned sheet. -/
theorem w2Bridge_mkk : W2Bridge degree coordinate chart graph label SourceCase.w2Mkk := by
  intro target data fullDim column hChart tracks hAdm star input classification hTag
  obtain ⟨z, hNonneg, hZeroCol, hRows⟩ := hAdm
  have hZero : z (fullDim.labelling.targetEdge.symm (contractedEdge fullDim column)) = 0 := by
    rw [targetEdge_symm_contractedEdge]; exact hZeroCol
  have hForest := SourceFibreForest.contractionForest_of_fullDimensional fullDim z hNonneg hRows
    (hc_column fullDim column) hZero
  have hConn : graph_connected (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) :=
    graph_connected_contract target (hab_column fullDim column) (hOne_column fullDim column)
      fullDim.targetConnected
  have hGen : genus (contract target (hab_column fullDim column)
      (hOne_column fullDim column)) = 0 :=
    (genus_contract target (hab_column fullDim column) (hOne_column fullDim column)).trans
      fullDim.targetGenus
  obtain ⟨wallBlock, wallProfile, wallShape, hBackground⟩ :=
    W2MkkGraphTracking.exists_w2Mkk_payload data (hc_column fullDim column)
      (hab_column fullDim column) (hOne_column fullDim column) star input classification hTag
  rcases W2MkkSourceCandidates.exists_firstMember_or_secondMember wallShape with
    hOrientation | hOrientation
  · obtain ⟨member⟩ := hOrientation
    obtain ⟨position, fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
      W2MkkGraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest input
        wallProfile hBackground
        (W2MkkSelectedCensus.divalent_endpoints data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim wallProfile
          wallShape).1
        (W2MkkSelectedCensus.divalent_endpoints data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim wallProfile
          wallShape).2.1
        wallShape member.toDetachData (W2MkkSourceCandidates.pinSheet wallProfile)
        (W2MkkSelectedCensus.selectedCensus_dichotomy data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest wallProfile
          wallShape member.toDetachData hBackground)
        tracks
    match position with
    | 0 =>
      exact ⟨TrackedWallProgressMore.trackedW2MkkFirst (wall := column) input wallShape member
        (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 0 fd
        ((A04MoreTags.mkkFirstFamily_wallColumn input wallShape member
          (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 0 fd).trans
          (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
    | 1 =>
      exact ⟨TrackedWallProgressMore.trackedW2MkkFirst (wall := column) input wallShape member
        (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 2 fd
        ((A04MoreTags.mkkFirstFamily_wallColumn input wallShape member
          (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 2 fd).trans
          (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
  · obtain ⟨member⟩ := hOrientation
    obtain ⟨position, fd, hMatrix, hWall, -, -, ⟨trackFd⟩⟩ :=
      W2MkkGraphTracking.exists_matched_tracking data (hc_column fullDim column)
        (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest input
        wallProfile hBackground
        (W2MkkSelectedCensus.divalent_endpoints data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim wallProfile
          wallShape).1
        (W2MkkSelectedCensus.divalent_endpoints data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim wallProfile
          wallShape).2.1
        wallShape member.toDetachData (W2MkkSourceCandidates.pinSheet wallProfile)
        (W2MkkSelectedCensus.selectedCensus_dichotomy data (hc_column fullDim column)
          (hab_column fullDim column) (hOne_column fullDim column) fullDim hForest wallProfile
          wallShape member.toDetachData hBackground)
        tracks
    match position with
    | 0 =>
      exact ⟨TrackedWallProgressMore.trackedW2MkkSecond (wall := column) input wallShape member
        (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 1 fd
        ((A04MoreTags.mkkSecondFamily_wallColumn input wallShape member
          (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 1 fd).trans
          (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩
    | 1 =>
      exact ⟨TrackedWallProgressMore.trackedW2MkkSecond (wall := column) input wallShape member
        (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 2 fd
        ((A04MoreTags.mkkSecondFamily_wallColumn input wallShape member
          (W2MkkSourceCandidates.pinSheet wallProfile) hConn hGen 2 fd).trans
          (hWall.trans (targetEdge_symm_contractedEdge fullDim column)))
        ⟨leftEnd fullDim column, hab_column fullDim column⟩ chart (hMatrix.trans hChart) trackFd⟩


/-- **The wall bridge at one chart, from the two trivalent tags alone.**
`InteriorProgress` discharges six of the ten per-tag bridges and this file the
two divalent ones, so `InteriorProgress.wallBridge_of_remaining` needs only
`w3Four` and `w3Shift`.  Composed with
`InteriorProgress.trackedClassified_of_state` and
`InteriorProgress.interior_of_bridges`, this is the whole of `interior` on those
two plus the march's three metric facts and the genericity condition
`SimpleNegativeCrossings`. -/
theorem wallBridge_of_trivalent
    (b3Four : W3Bridge degree coordinate chart graph label SourceCase.w3Four)
    (b3Shift : W3Bridge degree coordinate chart graph label SourceCase.w3Shift) :
    WallBridge degree coordinate chart graph label :=
  wallBridge_of_remaining b3Four b3Shift w2Bridge_m1k w2Bridge_mkk

/-- **Fit check against the caller.**  `wallBridge_of_trivalent` is literally
the `bridge` argument of `InteriorProgress.trackedClassified_of_state`, so the
tracked classification at a march state rests on the two trivalent tags, the
march's three metric facts and nothing else.  This theorem is that application, so the shape
is checked by Lean rather than asserted; `InteriorProgress.interior_of_bridges`
and `OuterWalk.coneEntry_of_reaches` take it from here. -/
theorem trackedClassified_of_state_of_trivalent
    {baseStart baseFinish : coordinate → ℚ}
    (current : TrackedState degree graph label
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      baseStart baseFinish)
    (b3Four : W3Bridge degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label) graph label SourceCase.w3Four)
    (b3Shift : W3Bridge degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label) graph label SourceCase.w3Shift)
    (hstart : ∀ i, 0 < baseStart i) (hfinish : ∀ i, 0 ≤ baseFinish i)
    (hrestart : 0 ≤ current.toMatrixState.restartTime) :
    TrackedWallProgressMore.TrackedClassified degree coordinate
      (MatrixAtlas.atlasMatrix current.toMatrixState.label)
      current.toMatrixState.currentStart current.toMatrixState.currentFinish
      graph label :=
  trackedClassified_of_state current (wallBridge_of_trivalent b3Four b3Shift)
    hstart hfinish hrestart

end

end DraismaVargas.LocalCases.InteriorBridgesDivalent
