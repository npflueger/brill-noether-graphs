import DraismaVargas.LocalCases.W3InteriorGraphTracking

/-!
# W3 anchored row coherence
The actual two-branch constructor of `W3FourFamilyMatching` is reconstructed
here solely to retain its concrete `ColumnData` witnesses. No new structure is
introduced, and the generic `FamilyMatching` interface is used as it stands.
-/

namespace DraismaVargas.LocalCases.W3TrackedAnchoring

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open FullDimensionalSource WallDegeneration
open W3R1SourceProfile
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3FourClosure (FourStarGeometry ofGrowProfile PositionOne PositionTwo)
open W3FourSurvival (SelectedSurvival branchSwap_sourceEdge_of_fixed
  branchSwap_sourceEdge_of_moved)
open W3FourStableGraph
open W3FourLimitRows
open W3FourRegrownColumn
open W3FourHonestBalance (HonestFigure28)
open W3FourStableIncidence (growDictionary positionOneDictionary positionTwoDictionary)
open LimitChainCore (Gauge)
open W3FourRegrownColumnSeam (MemberCertificates)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond
  thirdCandidate fourthCandidate)
open W3FourDisjointness (branchSwapOfPerm)
open W3FourIncomingCensus (WallMember positionOneMember positionTwoMember)
open W3FourIncomingMatching (figure28Members)
open W3ShiftIncomingMatching (SelectedCensus)


open W3FourFamilyMatching

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : ThreeStar target wall} {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- Required row coherence, not an existence assertion. Only nonsingular
members are compared, as selected by the real positive exit. -/
def RowsCompatible {geometry : FourStarGeometry data wall}
    (certified : MemberCertificates data wall geometry)
    (labelling : StablePathLabelling data) : Prop :=
  ∀ i : Fin 4,
    (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation i)).det ≠ 0 →
    (certified.receipts.labelling i).row =
      (certified.dictionary i).row.symm.trans labelling.row

/-- Literal natural-matrix compatibility of the actual dictionary, including
every named target occurrence. This is proved by the concrete constructors. -/
def NaturalRowsCompatible {geometry : FourStarGeometry data wall}
    (certified : MemberCertificates data wall geometry)
    (labelling : StablePathLabelling data) : Prop :=
  ∀ i : Fin 4,
    GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation i) =
    (StableSourceMatrix.matrix (certified.receipts.candidate i).datum).submatrix
      (labelling.row.symm.trans (certified.dictionary i).row)
      (occurrenceEquiv target wall (certified.receipts.candidate i).right)

theorem rowsCompatible_of_natural {geometry : FourStarGeometry data wall}
    (certified : MemberCertificates data wall geometry)
    (labelling : StablePathLabelling data)
    (h : NaturalRowsCompatible certified labelling) :
    RowsCompatible certified labelling := by
  intro i hDet
  exact (W3InteriorGraphTracking.honestLabelling_row_eq (certified.receipts.honest i)
    (labelling.row.symm.trans (certified.dictionary i).row) (h i) hDet).trans (by rfl)

theorem exists_tracked_anchoredCertificates_withExtra (hValid : data.Valid)
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraFirst)
    (extraFirst_separate : ¬(data.edgePartition profile.first.1.1.1).Rel
      profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraSecond)
    (extraSecond_separate : ¬(data.edgePartition profile.second.1.1.1).Rel
      profile.second.1.1.2 extraSecond)
    (positionPlan : PositionPlan data wall
      (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
        extraFirst extraFirst_wall extraFirst_separate)))
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true) :
    ∃ ac : AnchoredCertificatesWithExtra data wall input profile directions largest_index
      extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
      extraSecond_separate positionPlan,
      NaturalRowsCompatible ac.certified (StablePathLabelling.ofCardEq data input.stablePath_card) := by
  classical
  let grownFirst := (growProfileFirst profile directions largest_index).withExtra
    extraFirst extraFirst_wall extraFirst_separate
  let grownSecond := (growProfileSecond profile directions largest_index).withExtra
    extraSecond extraSecond_wall extraSecond_separate
  let geometry : FourStarGeometry data wall := ofGrowProfile grownFirst
  let labelling : StablePathLabelling data :=
    StablePathLabelling.ofCardEq data input.stablePath_card
  let rows : LimitRows data wall geometry := limitRowsOfInput grownFirst
  let gaugeRefl : Gauge data data wall := Gauge.refl data wall
  let cdThree : ColumnData data wall geometry labelling :=
    growColumnData grownFirst (SelectedSurvival.ofGrowProfile grownFirst) hValid
      geometry labelling rfl rows.rowGrow
      (growRow_eq_rowOf labelling grownFirst
        (SelectedSurvival.ofGrowProfile grownFirst)
        (W3FourLimitRows.grow_survives grownFirst)).symm geometry.growAnchor rfl
  let cdFour : ColumnData data wall geometry labelling :=
    growColumnData grownSecond (SelectedSurvival.ofGrowProfile grownSecond) hValid
      geometry labelling geometry.other_wall_rel rows.rowOther
      (growRow_eq_rowOf labelling grownSecond
        (SelectedSurvival.ofGrowProfile grownSecond)
        (W3FourLimitRows.other_survives grownFirst)).symm geometry.otherAnchor rfl
  cases positionPlan with
  | one hDisjoint =>
    -- `M⁽¹⁾` over the incoming datum, `M⁽²⁾` over a branch-swapped copy.
    let posn : PositionOne data wall :=
      { toFourStarGeometry := geometry, disjoint := hDisjoint }
    have survivalPosn : SelectedSurvival data wall posn.toFourStarGeometry :=
      SelectedSurvival.ofGrowProfile grownFirst
    have hRowGrow : rows.rowGrow =
        gaugeRow labelling gaugeRefl survivalPosn.grow_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeRefl survivalPosn.grow_survives
        (W3FourLimitRows.grow_survives grownFirst) ?_).symm
      exact GluingDatum.sourceEdge_self data grownFirst.grow.1
    have hRowOther : rows.rowOther =
        gaugeRow labelling gaugeRefl survivalPosn.other_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeRefl survivalPosn.other_survives
        (W3FourLimitRows.other_survives grownFirst) ?_).symm
      exact GluingDatum.sourceEdge_self data grownFirst.other.1
    let cdOne : ColumnData data wall geometry labelling :=
      positionOneColumnData posn survivalPosn hValid geometry labelling gaugeRefl
        rfl (fun _ ↦ rfl) rows.rowGrow rows.rowOther hRowGrow hRowOther
        geometry.growAnchor geometry.otherAnchor rfl rfl
    obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, hGeomTwo, _, _, hIndexTwo⟩ :=
      W3FourClosure.exists_member_two geometry root hRoot hGrowFixed hLargestFixed
        hOtherMoved
    have hWallTwo := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
      wall root hRoot permTwo hFixTwo
    let gaugeTwo : Gauge data
        (branchSwapOfPerm data wall root hRoot permTwo hFixTwo).apply wall :=
      Gauge.ofSheetRelabeling (branchSwapOfPerm data wall root hRoot permTwo hFixTwo)
        hValid.1 hWallTwo
    have hAnchorTwo : positionTwo.toFourStarGeometry.growAnchor =
        geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomTwo
    have hLargestTwo : positionTwo.toFourStarGeometry.largestTarget =
        geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomTwo
    have hLargestAnchorTwo : positionTwo.toFourStarGeometry.largestAnchor =
        geometry.largestAnchor := congrArg FourStarGeometry.largestAnchor hGeomTwo
    have survivalTwo : SelectedSurvival
        (branchSwapOfPerm data wall root hRoot permTwo hFixTwo).apply wall
          positionTwo.toFourStarGeometry := by
      rw [hGeomTwo]
      exact SelectedSurvival.swap geometry root hRoot permTwo hFixTwo
        (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
        hLargestFixed hOtherMoved
    have hValidTwo := hGaugeTwo.valid hValid
    have hBackgroundTwo : ∀ sheet : Fin degree,
        (branchSwapOfPerm data wall root hRoot permTwo
            hFixTwo).apply.sourceEdge positionTwo.largestTarget sheet =
          gaugeTwo.edge (data.sourceEdge positionTwo.largestTarget sheet) := by
      intro sheet
      rw [hLargestTwo]
      exact branchSwap_sourceEdge_of_fixed root hRoot permTwo hFixTwo
        geometry.largestTarget hLargestFixed sheet
    have hRowLargestTwo : rows.rowLargest =
        gaugeRow labelling gaugeTwo survivalTwo.largest_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeTwo survivalTwo.largest_survives
        (W3FourLimitRows.largest_survives grownFirst) ?_).symm
      rw [hLargestTwo, hLargestAnchorTwo, branchSwap_sourceEdge_of_fixed root hRoot
        permTwo hFixTwo geometry.largestTarget hLargestFixed geometry.largestAnchor]
      exact congrArg gaugeTwo.edge
        (GluingDatum.sourceEdge_self data grownFirst.largest.1)
    let cdTwo : ColumnData data wall geometry labelling :=
      positionTwoColumnData positionTwo survivalTwo hValidTwo geometry labelling
        gaugeTwo (by rw [hAnchorTwo]; exact rfl) hBackgroundTwo rows.rowLargest
        hRowLargestTwo geometry.growAnchor hAnchorTwo.symm
    have hRelTwo : ((branchSwapOfPerm data wall root hRoot permTwo
          hFixTwo).apply.vertexPartition wall).Rel
        positionTwo.toFourStarGeometry.growAnchor geometry.growAnchor :=
      congrArg ((branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply.vertexPartition wall).repr hAnchorTwo
    have hIdxOneGrow : newIndex (posn.toFourStarGeometry.reversedCandidate
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts) geometry.growAnchor =
        indexGrow geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard posn.toFourStarGeometry
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts
        (rfl : (data.vertexPartition wall).Rel geometry.growAnchor
          geometry.growAnchor)]
      exact (PositionOne.candidate_newEdge_blockCard posn).1
    have hIdxOneOther : newIndex (posn.toFourStarGeometry.reversedCandidate
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts) geometry.otherAnchor =
        indexOther geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard posn.toFourStarGeometry
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts geometry.other_wall_rel]
      exact (PositionOne.candidate_newEdge_blockCard posn).2
    have hIdxTwo : newIndex (positionTwo.toFourStarGeometry.reversedCandidate
        positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
        positionTwo.other_refines_fine positionTwo.rightCounts) geometry.growAnchor
        + 1 = indexGrow geometry + indexOther geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard positionTwo.toFourStarGeometry
        positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
        positionTwo.other_refines_fine positionTwo.rightCounts hRelTwo, hAnchorTwo]
      exact hIndexTwo
    refine ⟨
      { positionMember := positionOneMember posn survivalPosn
          input.distinguishedBlock.1 grownFirst.growAnchor_wall_rel
        positionMember_isolated := rfl
        positionMember_eq_plan := rfl
        positionMember_shape := Or.inl ⟨hDisjoint, rfl⟩
        certified :=
          { receipts :=
              { receipts :=
                  { rows := rows
                    member := ![cdOne.memberColumn, cdTwo.memberColumn,
                      cdThree.memberColumn, cdFour.memberColumn]
                    otherSheet := geometry.otherAnchor
                    background_one := rfl
                    selected_one := rfl
                    index_one_grow := hIdxOneGrow
                    index_one_other := hIdxOneOther
                    background_two := hLargestTwo
                    selected_two := rfl
                    index_two := hIdxTwo
                    background_three := rfl
                    selected_three := rfl
                    index_three := growCandidate_newIndex_grow grownFirst
                    background_four := rfl
                    selected_four := rfl
                    index_four := growCandidate_newIndex_grow grownSecond }
                honest := ?_ }
            dictionary := ?_
            memberGenus := ?_ }
        rows_eq := rfl
        base_three := rfl
        base_four := rfl
        candidate_three := HEq.rfl
        candidate_four := HEq.rfl
        index := 0
        base_index := rfl
        candidate_index := HEq.rfl }, ?_⟩
    · intro i
      fin_cases i
      · exact cdOne.isHonest
      · exact cdTwo.isHonest
      · exact cdThree.isHonest
      · exact cdFour.isHonest
    · intro i
      match i with
      | 0 => exact W3FourRowDescent.PositionOne.equivalence posn survivalPosn hValid
      | 1 => exact (positionTwoDictionary (branchSwapOfPerm data wall root
          hRoot permTwo hFixTwo) hValid.1 hGaugeTwo.valid positionTwo survivalTwo
          hValidTwo).equivalence
      | 2 => exact (growDictionary grownFirst
          (SelectedSurvival.ofGrowProfile grownFirst) hValid).equivalence
      | 3 => exact (growDictionary grownSecond
          (SelectedSurvival.ofGrowProfile grownSecond) hValid).equivalence
    · intro i
      match i with
      | 0 => exact PositionOne.candidate_sourceGenus posn
      | 1 => exact (positionTwoDictionary (branchSwapOfPerm data wall root
          hRoot permTwo hFixTwo) hValid.1 hGaugeTwo.valid positionTwo survivalTwo
          hValidTwo).sourceGenus
      | 2 => exact (growDictionary grownFirst
          (SelectedSurvival.ofGrowProfile grownFirst) hValid).sourceGenus
      | 3 => exact (growDictionary grownSecond
          (SelectedSurvival.ofGrowProfile grownSecond) hValid).sourceGenus
    · intro i
      fin_cases i
      · exact cdOne.presented_matrix_submatrix
      · exact cdTwo.presented_matrix_submatrix
      · exact cdThree.presented_matrix_submatrix
      · exact cdFour.presented_matrix_submatrix
  | two outside hOutWall hOutGrow hOutOther =>
    -- `M⁽²⁾` over the incoming datum, `M⁽¹⁾` over a branch-swapped copy.
    let posn : PositionTwo data wall :=
      { toFourStarGeometry := geometry, outside := outside, outside_wall := hOutWall,
        outside_grow := hOutGrow, outside_other := hOutOther }
    have survivalPosn : SelectedSurvival data wall posn.toFourStarGeometry :=
      SelectedSurvival.ofGrowProfile grownFirst
    have hRowLargest : rows.rowLargest =
        gaugeRow labelling gaugeRefl survivalPosn.largest_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeRefl survivalPosn.largest_survives
        (W3FourLimitRows.largest_survives grownFirst) ?_).symm
      exact GluingDatum.sourceEdge_self data grownFirst.largest.1
    let cdTwo : ColumnData data wall geometry labelling :=
      positionTwoColumnData posn survivalPosn hValid geometry labelling gaugeRefl
        rfl (fun _ ↦ rfl) rows.rowLargest hRowLargest geometry.growAnchor rfl
    obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, hGeomOne, _, _,
      hIndexOneGrow, hIndexOneOther⟩ :=
      W3FourClosure.exists_member_one geometry root hRoot hGrowFixed hLargestFixed
        hOtherMoved
    have hWallOne := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
      wall root hRoot permOne hFixOne
    let gaugeOne : Gauge data
        (branchSwapOfPerm data wall root hRoot permOne hFixOne).apply wall :=
      Gauge.ofSheetRelabeling (branchSwapOfPerm data wall root hRoot permOne hFixOne)
        hValid.1 hWallOne
    have hAnchorOne : positionOne.toFourStarGeometry.growAnchor =
        geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomOne
    have hGrowTargetOne : positionOne.toFourStarGeometry.growTarget =
        geometry.growTarget := congrArg FourStarGeometry.growTarget hGeomOne
    have hOtherTargetOne : positionOne.toFourStarGeometry.otherTarget =
        geometry.otherTarget := congrArg FourStarGeometry.otherTarget hGeomOne
    have hOtherAnchorOne : positionOne.toFourStarGeometry.otherAnchor =
        permOne geometry.otherAnchor :=
      congrArg FourStarGeometry.otherAnchor hGeomOne
    have hLargestOne : positionOne.toFourStarGeometry.largestTarget =
        geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomOne
    have survivalOne : SelectedSurvival
        (branchSwapOfPerm data wall root hRoot permOne hFixOne).apply wall
          positionOne.toFourStarGeometry := by
      rw [hGeomOne]
      exact SelectedSurvival.swap geometry root hRoot permOne hFixOne
        (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
        hLargestFixed hOtherMoved
    have hValidOne := hGaugeOne.valid hValid
    have hBackgroundOne : ∀ sheet : Fin degree,
        (branchSwapOfPerm data wall root hRoot permOne
            hFixOne).apply.sourceEdge positionOne.largestTarget sheet =
          gaugeOne.edge (data.sourceEdge positionOne.largestTarget sheet) := by
      intro sheet
      rw [hLargestOne]
      exact branchSwap_sourceEdge_of_fixed root hRoot permOne hFixOne
        geometry.largestTarget hLargestFixed sheet
    have hRowGrowOne : rows.rowGrow =
        gaugeRow labelling gaugeOne survivalOne.grow_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.grow_survives
        (W3FourLimitRows.grow_survives grownFirst) ?_).symm
      rw [hGrowTargetOne, hAnchorOne, branchSwap_sourceEdge_of_fixed root hRoot
        permOne hFixOne geometry.growTarget hGrowFixed geometry.growAnchor]
      exact congrArg gaugeOne.edge
        (GluingDatum.sourceEdge_self data grownFirst.grow.1)
    have hRowOtherOne : rows.rowOther =
        gaugeRow labelling gaugeOne survivalOne.other_survives := by
      refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.other_survives
        (W3FourLimitRows.other_survives grownFirst) ?_).symm
      rw [hOtherTargetOne, hOtherAnchorOne, branchSwap_sourceEdge_of_moved root hRoot
        permOne hFixOne geometry.otherTarget hOtherMoved geometry.otherAnchor]
      exact congrArg gaugeOne.edge
        (GluingDatum.sourceEdge_self data grownFirst.other.1)
    let cdOne : ColumnData data wall geometry labelling :=
      positionOneColumnData positionOne survivalOne hValidOne geometry labelling
        gaugeOne (by rw [hAnchorOne]; exact rfl) hBackgroundOne rows.rowGrow
        rows.rowOther hRowGrowOne hRowOtherOne geometry.growAnchor
        (permOne geometry.otherAnchor) hAnchorOne.symm hOtherAnchorOne.symm
    have hRelOne : ((branchSwapOfPerm data wall root hRoot permOne
          hFixOne).apply.vertexPartition wall).Rel
        positionOne.toFourStarGeometry.growAnchor geometry.growAnchor :=
      congrArg ((branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply.vertexPartition wall).repr hAnchorOne
    have hRelOther : ((branchSwapOfPerm data wall root hRoot
          permOne hFixOne).apply.vertexPartition wall).Rel
        positionOne.toFourStarGeometry.growAnchor (permOne geometry.otherAnchor) := by
      rw [hWallOne, hAnchorOne]
      exact geometry.other_wall_rel.trans (hFixOne geometry.otherAnchor).symm
    have hIdxOneGrow : newIndex (positionOne.toFourStarGeometry.reversedCandidate
        positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
        positionOne.other_refines_fine positionOne.rightCounts) geometry.growAnchor =
        indexGrow geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
        positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
        positionOne.other_refines_fine positionOne.rightCounts hRelOne, hAnchorOne]
      exact hIndexOneGrow
    have hIdxOneOther : newIndex (positionOne.toFourStarGeometry.reversedCandidate
        positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
        positionOne.other_refines_fine positionOne.rightCounts)
        (permOne geometry.otherAnchor) = indexOther geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
        positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
        positionOne.other_refines_fine positionOne.rightCounts hRelOther, hAnchorOne]
      exact hIndexOneOther
    have hIdxTwo : newIndex (posn.toFourStarGeometry.reversedCandidate
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts) geometry.growAnchor
        + 1 = indexGrow geometry + indexOther geometry := by
      rw [reversedCandidate_newIndex_eq_blockCard posn.toFourStarGeometry
        posn.fine posn.fine_refines posn.grow_refines_fine
        posn.other_refines_fine posn.rightCounts
        (rfl : (data.vertexPartition wall).Rel geometry.growAnchor
          geometry.growAnchor)]
      exact PositionTwo.candidate_newEdge_blockCard posn
    refine ⟨
      { positionMember := positionTwoMember posn survivalPosn
          input.distinguishedBlock.1 grownFirst.growAnchor_wall_rel
        positionMember_isolated := rfl
        positionMember_eq_plan := rfl
        positionMember_shape := Or.inr
          ⟨outside, hOutWall, hOutGrow, hOutOther, rfl⟩
        certified :=
          { receipts :=
              { receipts :=
                  { rows := rows
                    member := ![cdOne.memberColumn, cdTwo.memberColumn,
                      cdThree.memberColumn, cdFour.memberColumn]
                    otherSheet := permOne geometry.otherAnchor
                    background_one := hLargestOne
                    selected_one := rfl
                    index_one_grow := hIdxOneGrow
                    index_one_other := hIdxOneOther
                    background_two := rfl
                    selected_two := rfl
                    index_two := hIdxTwo
                    background_three := rfl
                    selected_three := rfl
                    index_three := growCandidate_newIndex_grow grownFirst
                    background_four := rfl
                    selected_four := rfl
                    index_four := growCandidate_newIndex_grow grownSecond }
                honest := ?_ }
            dictionary := ?_
            memberGenus := ?_ }
        rows_eq := rfl
        base_three := rfl
        base_four := rfl
        candidate_three := HEq.rfl
        candidate_four := HEq.rfl
        index := 1
        base_index := rfl
        candidate_index := HEq.rfl }, ?_⟩
    · intro i
      fin_cases i
      · exact cdOne.isHonest
      · exact cdTwo.isHonest
      · exact cdThree.isHonest
      · exact cdFour.isHonest
    · intro i
      match i with
      | 0 => exact (positionOneDictionary (branchSwapOfPerm data wall root
          hRoot permOne hFixOne) hValid.1 hGaugeOne.valid positionOne survivalOne
          hValidOne).equivalence
      | 1 => exact W3FourRowDescent.PositionTwo.equivalence posn survivalPosn hValid
      | 2 => exact (growDictionary grownFirst
          (SelectedSurvival.ofGrowProfile grownFirst) hValid).equivalence
      | 3 => exact (growDictionary grownSecond
          (SelectedSurvival.ofGrowProfile grownSecond) hValid).equivalence
    · intro i
      match i with
      | 0 => exact (positionOneDictionary (branchSwapOfPerm data wall root
          hRoot permOne hFixOne) hValid.1 hGaugeOne.valid positionOne survivalOne
          hValidOne).sourceGenus
      | 1 => exact PositionTwo.candidate_sourceGenus posn
      | 2 => exact (growDictionary grownFirst
          (SelectedSurvival.ofGrowProfile grownFirst) hValid).sourceGenus
      | 3 => exact (growDictionary grownSecond
          (SelectedSurvival.ofGrowProfile grownSecond) hValid).sourceGenus
    · intro i
      fin_cases i
      · exact cdOne.presented_matrix_submatrix
      · exact cdTwo.presented_matrix_submatrix
      · exact cdThree.presented_matrix_submatrix
      · exact cdFour.presented_matrix_submatrix

end DraismaVargas.LocalCases.W3TrackedAnchoring
