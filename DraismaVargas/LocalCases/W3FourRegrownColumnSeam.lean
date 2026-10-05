module

public import DraismaVargas.LocalCases.W3FourStableIncidence

@[expose] public section

/-!
# Figure 28's honest receipts, carrying their own dictionaries

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a=k₄)}` and Figure 28.
Part I works with isomorphism classes of gluing data; for a fixed gluing datum
value Figure 28's members live over branch-swapped copies of the wall datum.

`W3FourRegrownColumn.exists_figure28Receipts_honest` and
`W3FourStableIncidence.exists_figure28Dictionaries` are two existentials over
**one** construction: both `obtain` Figure 28's `M⁽¹⁾` and `M⁽²⁾` from
`W3FourClosure.exists_member_one` / `exists_member_two` on exactly the same
hypotheses, and both then instantiate `W3FourRowDescent`'s three row-descent
packages.  Because each is an `Exists`, the two sets of witnesses are
unrelated once the existentials are opened, so
`W3FourStableIncidence.HonestFigure28Exit.presentationAt` has to take the
member-to-member dictionary and the two source-genus receipts as
**hypotheses**, and `A04MoreTags.w3FourSupply` has to carry them as seam
hypotheses `certificate`, `memberGenus`.

This module removes that seam: it runs the construction **once** and hands back
the honest receipts together with the four
stable-incidence dictionaries and the four source-genus receipts, bundled as
`MemberCertificates`.  Nothing new is proved about Figure 28; the proof of
`exists_memberCertificates` is `exists_figure28Receipts_honest`'s own, with the
four `W3FourStableIncidence` packages built on the same witnesses instead of on
fresh ones.

## Why the bundle is a structure and not a conjunction

`StableGraphIncidence.Equivalence` is data, not a proposition, so
`∃ receipts, (∀ i j, Equivalence …)` is not even a statement.
`MemberCertificates` carries the equivalences as fields; the remaining clauses
of `exists_figure28Receipts_honest` -- the limit's own rows, the two grow
members' identifications, and the two bases -- stay propositional and are
returned beside it.

## What this adds beyond the two existentials

* `MemberCertificates.certificate` -- the sixteen member-to-member dictionaries
  `HonestFigure28Exit.presentationAt` asks for, on the honest receipts' own
  members rather than on a second, unrelated copy of them.
* `MemberCertificates.memberGenus` -- the four source-genus receipts.
* `base_three`, `base_four` -- `M⁽³⁾` and `M⁽⁴⁾` live over the **incoming
  datum itself**, not over a gauge copy.  `exists_figure28Receipts_honest`
  proves this (`(receipts.member 2).base = data` is one of its `rfl`s) but
  `W3FourHonestBalance.exists_honestFigure28` drops it, which is why its `HEq`
  clauses cannot be turned into equalities downstream.
* `exists_valid_positive_exit_presentation` -- Figure 28's certified positive
  exit with a full-dimensional presentation of the outgoing member attached,
  on **no** seam hypothesis at all.

## What this does *not* claim

Nothing here identifies the incoming member, transports the exit to the
original coordinates, or asserts that any member is nonsingular: the exit keeps
its own `det ≠ 0` gate on the selected member.  Nothing here is new
mathematics; it is a re-derivation that keeps two witnesses equal.
-/

namespace DraismaVargas.LocalCases.W3FourRegrownColumnSeam

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open FullDimensionalSource
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSurvival
open W3FourStableGraph
open W3FourLimitRows
open W3FourRegrownColumn
open W3FourHonestBalance (HonestFigure28)
open W3FourStableIncidence (MemberDictionary growDictionary positionOneDictionary
  positionTwoDictionary)
open LimitChainCore (Gauge GraphData sourceEdge_of_target)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- **Figure 28's honest receipts, with the dictionaries their exit needs.**

`certificate` is the member-to-member stable-incidence dictionary
`W3FourStableIncidence.HonestFigure28Exit.presentationAt` consumes and
`memberGenus` the two source-genus receipts it consumes beside it; both are
about the receipts' **own** members, which is the whole point of the bundle. -/
structure MemberCertificates (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) where
  /-- Figure 28's four members over the limit's own stable rows, honestly
  presented. -/
  receipts : HonestFigure28 data wall geometry
  /-- Each member's stable incidence graph is the incoming datum's. -/
  dictionary : ∀ i : Fin 4,
    StableGraphIncidence.Equivalence data (receipts.candidate i).datum
  /-- and each preserves the complete quotient-source genus. -/
  memberGenus : ∀ i : Fin 4,
    genus (receipts.candidate i).datum.sourceGraph = genus data.sourceGraph

namespace MemberCertificates

variable {geometry : FourStarGeometry data wall}
  (certified : MemberCertificates data wall geometry)

/-- **The sixteen member-to-member dictionaries**, as
`HonestFigure28Exit.presentationAt` asks for them: the composite of the two
members' dictionaries to the incoming datum, one reversed.  The incoming datum
is never an admissible transport *source* (its expanded target has one edge
fewer), which is why every dictionary the exit uses is of this shape. -/
noncomputable def certificate (i j : Fin 4) :
    StableGraphIncidence.Equivalence (certified.receipts.candidate i).datum
      (certified.receipts.candidate j).datum :=
  (certified.dictionary i).symm.trans (certified.dictionary j)

/-- **Figure 28's certified positive exit with the outgoing member's
full-dimensional presentation, on no seam hypothesis.**

`W3FourStableIncidence.HonestFigure28Exit.exists_valid_positive_exit_presentation`
verbatim, with `certificate` and `memberGenus` supplied by the bundle instead of
assumed.  So Equation (2)'s exit hands back a member that is valid, strictly
opposite in determinant sign, positively reachable with a cleared pencil, **and**
full-dimensionally presented in the honest coordinates -- from the receipts
alone. -/
theorem exists_valid_positive_exit_presentation
    (hValid : data.Valid) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root : target.V) (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation
      (certified.receipts.candidate incoming).datum (Option target.edges))
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (certified.receipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (z incomingVelocity : Option target.edges → ℚ)
    (outgoingVelocity : Fin 4 → Option target.edges → ℚ)
    (hz : z none = 0) (hzpos : ∀ i, i ≠ none → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (certified.receipts.gaugeFamily.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (certified.receipts.gaugeFamily.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (certified.receipts.gaugeFamily.presentation outgoing)).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity none < 0) :
    ∃ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
          (certified.receipts.gaugeFamily.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (certified.receipts.gaugeFamily.presentation outgoing)).det < 0 ∧
      (∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (certified.receipts.candidate outgoing)
          (certified.receipts.gaugeFamily.presentation outgoing)
          (z + t • outgoingVelocity outgoing))) ∧
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (certified.receipts.candidate outgoing).datum (Option target.edges),
        GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix
            (certified.receipts.gaugeFamily.presentation outgoing) :=
  W3FourStableIncidence.HonestFigure28Exit.exists_valid_positive_exit_presentation
    certified.receipts certified.certificate certified.memberGenus hValid hConnected
    hGenus root incoming incomingFD hincoming z incomingVelocity outgoingVelocity hz
    hzpos hSystems hIncomingDirection

end MemberCertificates

section Existence

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

open W3FourSourceCandidates (growProfileFirst growProfileSecond thirdCandidate
  fourthCandidate)

/-- **The seam, closed.**  `W3FourRegrownColumn.exists_figure28Receipts_honest`
run once, with `W3FourStableIncidence`'s four packages built on its own
witnesses, so that the dictionaries and the source-genus receipts are about the
receipts' own members.

The hypotheses are character for character those of
`exists_figure28Receipts_honest`, `W3FourHonestBalance.exists_honestFigure28`
and `W3FourStableIncidence.exists_figure28Dictionaries`; the conclusion is the
conjunction of all three, with the two bases of `M⁽³⁾`, `M⁽⁴⁾` retained. -/
theorem exists_memberCertificates_withExtra_origins (hValid : data.Valid)
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
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
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true) :
    ∃ certified : MemberCertificates data wall
        (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
          extraFirst extraFirst_wall extraFirst_separate)),
      certified.receipts.receipts.rows =
          limitRowsOfInput ((growProfileFirst profile directions largest_index).withExtra
            extraFirst extraFirst_wall extraFirst_separate) ∧
        certified.receipts.base 2 = data ∧ certified.receipts.base 3 = data ∧
        HEq (certified.receipts.candidate 2)
          ((growProfileFirst profile directions largest_index).withExtra extraFirst
            extraFirst_wall extraFirst_separate).growCandidate ∧
        HEq (certified.receipts.candidate 3)
          ((growProfileSecond profile directions largest_index).withExtra extraSecond
            extraSecond_wall extraSecond_separate).growCandidate ∧
        (∃ (permutation : Equiv.Perm (Fin degree))
          (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
          (position : W3FourClosure.PositionOne
            (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
          position.toFourStarGeometry =
            (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
              extraFirst extraFirst_wall extraFirst_separate)).swap root hRoot permutation hFix
                hGrowFixed hLargestFixed hOtherMoved ∧
          certified.receipts.base 0 =
            (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permutation hFix).apply ∧
          HEq (certified.receipts.candidate 0) position.candidate) ∧
        (∃ (permutation : Equiv.Perm (Fin degree))
          (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
          (position : W3FourClosure.PositionTwo
            (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
          position.toFourStarGeometry =
            (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
              extraFirst extraFirst_wall extraFirst_separate)).swap root hRoot permutation hFix
                hGrowFixed hLargestFixed hOtherMoved ∧
          certified.receipts.base 1 =
            (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permutation hFix).apply ∧
          HEq (certified.receipts.candidate 1) position.candidate) := by
  classical
  let grownFirst := (W3FourSourceCandidates.growProfileFirst profile directions
    largest_index).withExtra extraFirst extraFirst_wall extraFirst_separate
  let grownSecond := (W3FourSourceCandidates.growProfileSecond profile directions
    largest_index).withExtra extraSecond extraSecond_wall extraSecond_separate
  let geometry : FourStarGeometry data wall := ofGrowProfile grownFirst
  let labelling : StablePathLabelling data :=
    StablePathLabelling.ofCardEq data input.stablePath_card
  let rows : LimitRows data wall geometry := limitRowsOfInput grownFirst
  obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, hGeomOne, _, _,
    hIndexOneGrow, hIndexOneOther⟩ :=
    W3FourClosure.exists_member_one geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, hGeomTwo, _, _, hIndexTwo⟩ :=
    W3FourClosure.exists_member_two geometry root hRoot hGrowFixed hLargestFixed
      hOtherMoved
  have hWallOne := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
    wall root hRoot permOne hFixOne
  have hWallTwo := W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall data
    wall root hRoot permTwo hFixTwo
  let gaugeOne : Gauge data
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply wall :=
    Gauge.ofSheetRelabeling (W3FourDisjointness.branchSwapOfPerm data wall root
      hRoot permOne hFixOne) hValid.1 hWallOne
  let gaugeTwo : Gauge data
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply wall :=
    Gauge.ofSheetRelabeling (W3FourDisjointness.branchSwapOfPerm data wall root
      hRoot permTwo hFixTwo) hValid.1 hWallTwo
  have hAnchorOne : positionOne.toFourStarGeometry.growAnchor =
      geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomOne
  have hAnchorTwo : positionTwo.toFourStarGeometry.growAnchor =
      geometry.growAnchor := congrArg FourStarGeometry.growAnchor hGeomTwo
  have hGrowTargetOne : positionOne.toFourStarGeometry.growTarget =
      geometry.growTarget := congrArg FourStarGeometry.growTarget hGeomOne
  have hOtherTargetOne : positionOne.toFourStarGeometry.otherTarget =
      geometry.otherTarget := congrArg FourStarGeometry.otherTarget hGeomOne
  have hOtherAnchorOne : positionOne.toFourStarGeometry.otherAnchor =
      permOne geometry.otherAnchor :=
    congrArg FourStarGeometry.otherAnchor hGeomOne
  have hLargestOne : positionOne.toFourStarGeometry.largestTarget =
      geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomOne
  have hLargestTwo : positionTwo.toFourStarGeometry.largestTarget =
      geometry.largestTarget := congrArg FourStarGeometry.largestTarget hGeomTwo
  have hLargestAnchorTwo : positionTwo.toFourStarGeometry.largestAnchor =
      geometry.largestAnchor :=
    congrArg FourStarGeometry.largestAnchor hGeomTwo
  have survivalOne : SelectedSurvival
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply wall positionOne.toFourStarGeometry := by
    rw [hGeomOne]
    exact SelectedSurvival.swap geometry root hRoot permOne hFixOne
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  have survivalTwo : SelectedSurvival
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply wall positionTwo.toFourStarGeometry := by
    rw [hGeomTwo]
    exact SelectedSurvival.swap geometry root hRoot permTwo hFixTwo
      (SelectedSurvival.ofGrowProfile grownFirst) hValid.1 hGrowFixed
      hLargestFixed hOtherMoved
  have hValidOne := hGaugeOne.valid hValid
  have hValidTwo := hGaugeTwo.valid hValid
  have hBackgroundOne : ∀ sheet : Fin degree,
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
          hFixOne).apply.sourceEdge positionOne.largestTarget sheet =
        gaugeOne.edge (data.sourceEdge positionOne.largestTarget sheet) := by
    intro sheet
    rw [hLargestOne]
    exact branchSwap_sourceEdge_of_fixed root hRoot permOne hFixOne
      geometry.largestTarget hLargestFixed sheet
  have hBackgroundTwo : ∀ sheet : Fin degree,
      (W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
          hFixTwo).apply.sourceEdge positionTwo.largestTarget sheet =
        gaugeTwo.edge (data.sourceEdge positionTwo.largestTarget sheet) := by
    intro sheet
    rw [hLargestTwo]
    exact branchSwap_sourceEdge_of_fixed root hRoot permTwo hFixTwo
      geometry.largestTarget hLargestFixed sheet
  have hRowGrowOne : rows.rowGrow =
      gaugeRow labelling gaugeOne survivalOne.grow_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.grow_survives
      (W3FourLimitRows.grow_survives grownFirst) ?_).symm
    rw [hGrowTargetOne, hAnchorOne, branchSwap_sourceEdge_of_fixed root hRoot
      permOne hFixOne geometry.growTarget hGrowFixed geometry.growAnchor]
    exact congrArg gaugeOne.edge (GluingDatum.sourceEdge_self data grownFirst.grow.1)
  have hRowOtherOne : rows.rowOther =
      gaugeRow labelling gaugeOne survivalOne.other_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeOne survivalOne.other_survives
      (W3FourLimitRows.other_survives grownFirst) ?_).symm
    rw [hOtherTargetOne, hOtherAnchorOne, branchSwap_sourceEdge_of_moved root hRoot
      permOne hFixOne geometry.otherTarget hOtherMoved geometry.otherAnchor]
    exact congrArg gaugeOne.edge
      (GluingDatum.sourceEdge_self data grownFirst.other.1)
  have hRowLargestTwo : rows.rowLargest =
      gaugeRow labelling gaugeTwo survivalTwo.largest_survives := by
    refine (gaugeRow_eq_of_edge labelling gaugeTwo survivalTwo.largest_survives
      (W3FourLimitRows.largest_survives grownFirst) ?_).symm
    rw [hLargestTwo, hLargestAnchorTwo, branchSwap_sourceEdge_of_fixed root hRoot
      permTwo hFixTwo geometry.largestTarget hLargestFixed geometry.largestAnchor]
    exact congrArg gaugeTwo.edge
      (GluingDatum.sourceEdge_self data grownFirst.largest.1)
  let cdOne : ColumnData data wall geometry labelling :=
    positionOneColumnData positionOne survivalOne hValidOne geometry labelling
      gaugeOne (by rw [hAnchorOne]; exact rfl) hBackgroundOne rows.rowGrow rows.rowOther
      hRowGrowOne hRowOtherOne geometry.growAnchor (permOne geometry.otherAnchor)
      hAnchorOne.symm hOtherAnchorOne.symm
  let cdTwo : ColumnData data wall geometry labelling :=
    positionTwoColumnData positionTwo survivalTwo hValidTwo geometry labelling
      gaugeTwo (by rw [hAnchorTwo]; exact rfl) hBackgroundTwo rows.rowLargest hRowLargestTwo
      geometry.growAnchor hAnchorTwo.symm
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
  have hRelOne : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
        hFixOne).apply.vertexPartition wall).Rel
      positionOne.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permOne
      hFixOne).apply.vertexPartition wall).repr hAnchorOne
  have hRelTwo : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
        hFixTwo).apply.vertexPartition wall).Rel
      positionTwo.toFourStarGeometry.growAnchor geometry.growAnchor :=
    congrArg ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot permTwo
      hFixTwo).apply.vertexPartition wall).repr hAnchorTwo
  have hRelOther : ((W3FourDisjointness.branchSwapOfPerm data wall root hRoot
        permOne hFixOne).apply.vertexPartition wall).Rel
      positionOne.toFourStarGeometry.growAnchor (permOne geometry.otherAnchor) := by
    rw [hWallOne, hAnchorOne]
    exact geometry.other_wall_rel.trans (hFixOne geometry.otherAnchor).symm
  have hIdxOneGrow : newIndex (positionOne.toFourStarGeometry.reversedCandidate
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts) geometry.growAnchor =
      (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts hRelOne, hAnchorOne]
    exact hIndexOneGrow
  have hIdxOneOther : newIndex (positionOne.toFourStarGeometry.reversedCandidate
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts)
      (permOne geometry.otherAnchor) =
      (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionOne.toFourStarGeometry
      positionOne.fine positionOne.fine_refines positionOne.grow_refines_fine
      positionOne.other_refines_fine positionOne.rightCounts hRelOther, hAnchorOne]
    exact hIndexOneOther
  have hIdxTwo : newIndex (positionTwo.toFourStarGeometry.reversedCandidate
      positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
      positionTwo.other_refines_fine positionTwo.rightCounts) geometry.growAnchor
      + 1 =
      (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor +
        (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor := by
    rw [reversedCandidate_newIndex_eq_blockCard positionTwo.toFourStarGeometry
      positionTwo.fine positionTwo.fine_refines positionTwo.grow_refines_fine
      positionTwo.other_refines_fine positionTwo.rightCounts hRelTwo, hAnchorTwo]
    exact hIndexTwo
  refine ⟨{ receipts :=
              { receipts :=
                  { rows := rows
                    member := ![cdOne.memberColumn, cdTwo.memberColumn,
                      cdThree.memberColumn, cdFour.memberColumn]
                    otherSheet := permOne geometry.otherAnchor
                    background_one := hLargestOne
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
            memberGenus := ?_ }, rfl, rfl, rfl, HEq.rfl, HEq.rfl,
      ⟨permOne, hFixOne, positionOne, hGeomOne, rfl, HEq.rfl⟩,
      ⟨permTwo, hFixTwo, positionTwo, hGeomTwo, rfl, HEq.rfl⟩⟩
  · intro i
    fin_cases i
    · exact cdOne.isHonest
    · exact cdTwo.isHonest
    · exact cdThree.isHonest
    · exact cdFour.isHonest
  · intro i
    match i with
    | 0 => exact (positionOneDictionary (W3FourDisjointness.branchSwapOfPerm data wall root
        hRoot permOne hFixOne) hValid.1 hGaugeOne.valid positionOne survivalOne
        hValidOne).equivalence
    | 1 => exact (positionTwoDictionary (W3FourDisjointness.branchSwapOfPerm data wall root
        hRoot permTwo hFixTwo) hValid.1 hGaugeTwo.valid positionTwo survivalTwo
        hValidTwo).equivalence
    | 2 => exact (growDictionary grownFirst (SelectedSurvival.ofGrowProfile grownFirst)
        hValid).equivalence
    | 3 => exact (growDictionary grownSecond (SelectedSurvival.ofGrowProfile grownSecond)
        hValid).equivalence
  · intro i
    match i with
    | 0 => exact (positionOneDictionary (W3FourDisjointness.branchSwapOfPerm data wall root
        hRoot permOne hFixOne) hValid.1 hGaugeOne.valid positionOne survivalOne
        hValidOne).sourceGenus
    | 1 => exact (positionTwoDictionary (W3FourDisjointness.branchSwapOfPerm data wall root
        hRoot permTwo hFixTwo) hValid.1 hGaugeTwo.valid positionTwo survivalTwo
        hValidTwo).sourceGenus
    | 2 => exact (growDictionary grownFirst (SelectedSurvival.ofGrowProfile grownFirst)
        hValid).sourceGenus
    | 3 => exact (growDictionary grownSecond (SelectedSurvival.ofGrowProfile grownSecond)
        hValid).sourceGenus

/-- Compatibility statement, forgetting only the two reversed-member origins.
The stronger constructor above keeps them for actual denominator consumers. -/
theorem exists_memberCertificates_withExtra (hValid : data.Valid)
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extraFirst)
    (extraFirst_separate : ¬(data.edgePartition profile.first.1.1.1).Rel
      profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extraSecond)
    (extraSecond_separate : ¬(data.edgePartition profile.second.1.1.1).Rel
      profile.second.1.1.2 extraSecond)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed : TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true) :
    ∃ certified : MemberCertificates data wall
        (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
          extraFirst extraFirst_wall extraFirst_separate)),
      certified.receipts.receipts.rows =
          limitRowsOfInput ((growProfileFirst profile directions largest_index).withExtra
            extraFirst extraFirst_wall extraFirst_separate) ∧
        certified.receipts.base 2 = data ∧ certified.receipts.base 3 = data ∧
        HEq (certified.receipts.candidate 2)
          ((growProfileFirst profile directions largest_index).withExtra extraFirst
            extraFirst_wall extraFirst_separate).growCandidate ∧
        HEq (certified.receipts.candidate 3)
          ((growProfileSecond profile directions largest_index).withExtra extraSecond
            extraSecond_wall extraSecond_separate).growCandidate := by
  obtain ⟨certified, hRows, hBase3, hBase4, hThree, hFour, _, _⟩ :=
    exists_memberCertificates_withExtra_origins hValid profile directions largest_index
      extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
      extraSecond_separate root hRoot hGrowFixed hLargestFixed hOtherMoved
  exact ⟨certified, hRows, hBase3, hBase4, hThree, hFour⟩

/-- The original Figure 28 certificate theorem, recovered by retaining the
default transferred sheets chosen by the two canonical grow profiles. -/
theorem exists_memberCertificates (hValid : data.Valid)
    (profile : W3R1SourceProfile.Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true) :
    ∃ certified : MemberCertificates data wall
        (ofGrowProfile (growProfileFirst profile directions largest_index)),
      certified.receipts.receipts.rows =
          limitRowsOfInput (growProfileFirst profile directions largest_index) ∧
        certified.receipts.base 2 = data ∧ certified.receipts.base 3 = data ∧
        HEq (certified.receipts.candidate 2)
          (thirdCandidate profile directions largest_index) ∧
        HEq (certified.receipts.candidate 3)
          (fourthCandidate profile directions largest_index) := by
  let first := growProfileFirst profile directions largest_index
  let second := growProfileSecond profile directions largest_index
  have result := exists_memberCertificates_withExtra hValid profile directions largest_index
      first.extraSheet first.extraSheet_wall_rel first.extraSheet_separate
      second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
      root hRoot hGrowFixed hLargestFixed hOtherMoved
  have hFirst := first.withExtra_self
  have hSecond := second.withExtra_self
  rw [hFirst, hSecond] at result
  exact result

end Existence

end DraismaVargas.LocalCases.W3FourRegrownColumnSeam
