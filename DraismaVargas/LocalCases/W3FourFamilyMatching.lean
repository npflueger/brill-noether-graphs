import DraismaVargas.LocalCases.W3FourHonestReceipts

/-!
# Figure 28's family matching at the `t₄` index

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a=k₄)}`, Figure 28 and
Equation (2).  Part I works with isomorphism classes of gluing data; for a fixed
gluing datum value Equation (2)'s members need not all live over one datum.

## The matching this file proves

`W3FourHonestReceipts.FamilyMatching` is what remains of `hHonest` once
`W3FourHonestReceipts` restates Equation (2)'s family at an arbitrary stable
labelling, and `W3FourHonestReceipts.familyMatching_of_position` reduces it to
the **`t₄` index alone**: at the two Position II.a indices the incoming
family's member and Equation (2)'s member are literally the same object, while
at `t₄` the incoming family's member is `W3FourIncomingCensus.positionOneMember`
or `positionTwoMember` over `contractDatum data hc hab hOne` itself
(`exists_positionMember`: exactly one of the two exists over any datum of the
case) and Equation (2)'s `M⁽¹⁾`, `M⁽²⁾` live over *branch-swapped copies*
(`W3FourRegrownColumnSeam.exists_memberCertificates`, through
`W3FourClosure.exists_member_one` / `exists_member_two`).  That mismatch comes
from working with fixed gluing data rather than isomorphism classes: Equation
(2) needs both members over one datum.

## How: anchor the family, do not transport the member

The obvious route -- transport the incoming member's presentation across the
branch swap with `W3FourDisjointness.fullDimensional_gauge` and
`RelabelFullDimensional.sheet_matrix_eq` -- is **not available**, and not for
want of a lemma.  Those two carry a presentation of the *wall* datum to its
branch swap, because `branchSwapOfPerm`'s permutation preserves the blocks of
`data.vertexPartition wall` (its `hFix`).  A presentation of a **member's**
datum lives over the *expanded* target, so using them there would first ask for
the swap lifted through `TargetExpansion` -- the Figure 28 analogue of
`W3ShiftIncomingTransport.contract_swappedDatum`, one level up instead of one
level down -- and `GluingDatum.SheetRelabeling.ofRegion`'s boundary obligation
at the **trivalent** endpoint is then `position.fine.Rel (permutation sheet)
sheet`.  (`right` is `W3Nd2SourceCandidates.rightOf geometry.largestTarget`, so
`t₂` and `t₃` sit at the fresh vertex, whose partition is
`(fineResolution _ position.fine _).reverse.right = position.fine`, and `t₃` is
the one direction the swap moves; the fresh vertex must stay unmoved for the
relabelled datum to be the swapped member's at all.)  That obligation is
strictly stronger than `hFix`, and exactly where Position I needs the swap --
when `e₂` and `e₃` meet -- it cannot hold: a permutation preserving the blocks
of `fine` maps `A₀ ∖ e₂` to itself, so it cannot carry `e₃` off `e₂` unless
`e₃` was off it already.  So the branch swap is a gauge of the wall datum and
not of the member, which is the same wall the shift case hit one level down at
`W3ShiftIncomingTransport.EndsCompatible`.

What is available instead is a **choice** in the construction of Equation (2)'s
own receipts.  `W3FourRegrownColumn.positionOneColumnData` and
`positionTwoColumnData` are stated for an arbitrary base and an arbitrary
`LimitChainCore.Gauge data base wall`; `exists_memberCertificates` instantiates
both at a branch-swapped copy, but only **one** of the two members needs a copy
-- whichever of Position I and Position II.b fails to exist over the incoming
datum -- and the other can be built over the incoming datum itself with
`LimitChainCore.Gauge.refl`.  `exists_anchoredCertificates` does exactly that:
it re-runs `exists_memberCertificates`'s construction under the case dichotomy
`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`, putting the
available member at `base = data` with the identity gauge and swapping only the
unavailable one, and returns **the incoming family's own `t₄` member beside
it**, with `base index = data` and `HEq` of the two candidates.  Then
`W3FourHonestReceipts.exists_transported` -- `subst` and nothing else --
discharges the `t₄` case of `familyMatching_of_position` exactly as it already
discharges the two Position II.a cases.

Nothing is transported across the swap, and no new geometry is proved: every
step is `W3FourRegrownColumn`'s, `W3FourRowDescent`'s and
`W3FourStableIncidence`'s own, re-run at a second instantiation of their
already-general base and gauge arguments.

## What is proved

* `AnchoredCertificates` and `exists_anchoredCertificates` -- Equation (2)'s
  honest receipts with their four dictionaries and source-genus receipts, together
  with the incoming family's `t₄` member and the index of Equation (2) at which
  the two coincide.  `exists_memberCertificates`'s own five conclusions are
  retained verbatim.
* `familyMatching` -- `W3FourHonestReceipts.FamilyMatching`, inhabited, for the
  identification family `W3FourIncomingMatching.figure28Members` built on the
  bundle's own `positionMember`.
* `AnchoredCertificatesWithExtra`, `exists_anchoredCertificates_withExtra` and
  `familyMatching_withExtra` -- the same for a Figure 28 family whose two
  Position II.a members carry prescribed transferred sheets, which is the form
  `W3FourClosureFinal` uses to reach the original-coordinate positive exit.

## What is not claimed

The selected-block census `W3ShiftIncomingMatching.SelectedCensus` is carried
verbatim and is **not** discharged here (`W3FourClosureFinal` supplies it).  No
requested `Spec`, no terminal refinement and no metric-length dictionary: the
cleared pencil is on the outgoing member's literal source subdivision, exactly
as in nd2, nd3, M11 and Figure 29.  `W3FourClosure`, `W3FourRegrownColumn`,
`W3FourRegrownColumnSeam` and `W3FourHonestReceipts` are consumed through their
public names only.
-/

namespace DraismaVargas.LocalCases.W3FourFamilyMatching

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

/-! ## §1  Equation (2)'s receipts, anchored at the incoming `t₄` member -/

section Anchored

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : ThreeStar target wall} {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The literal `t₄` member to anchor over the incoming datum: Position I
when the two smaller classes are disjoint, or Position II.b with a specified
outside sheet. -/
inductive PositionPlan (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) : Type
  | one (disjoint : Disjoint
      ((data.edgePartition geometry.growTarget).block geometry.growAnchor)
      ((data.edgePartition geometry.otherTarget).block geometry.otherAnchor))
  | two (outside : Fin degree)
      (outside_wall : (data.vertexPartition wall).Rel geometry.growAnchor outside)
      (outside_grow : ¬(data.edgePartition geometry.growTarget).Rel
        geometry.growAnchor outside)
      (outside_other : ¬(data.edgePartition geometry.otherTarget).Rel
        geometry.otherAnchor outside)

namespace PositionPlan

variable {geometry : FourStarGeometry data wall}

/-- The wall member named by an anchoring plan. -/
noncomputable def member {star : ThreeStar target wall}
    {input : W3SourceInput data star} (plan : PositionPlan data wall geometry)
    (survival : SelectedSurvival data wall geometry)
    (hRoot : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      geometry.growAnchor) :
    WallMember data wall input.distinguishedBlock.1 :=
  match plan with
  | .one hDisjoint => positionOneMember
      { toFourStarGeometry := geometry, disjoint := hDisjoint }
      survival input.distinguishedBlock.1 hRoot
  | .two outside hWall hGrow hOther => positionTwoMember
      { toFourStarGeometry := geometry, outside := outside, outside_wall := hWall,
        outside_grow := hGrow, outside_other := hOther }
      survival input.distinguishedBlock.1 hRoot

end PositionPlan

/-- **Equation (2)'s honest receipts together with the incoming family's `t₄`
member, over one datum.**

`receipts`, `rows_eq`, `base_three`, `base_four`, `candidate_three` and
`candidate_four` are `W3FourRegrownColumnSeam.exists_memberCertificates`'s own
conclusions, character for character.  What is added is `positionMember` --
the `t₄` member of the *incoming* identification family, the one
`W3FourIncomingCensus.exists_positionMember` supplies over the incoming datum
itself -- and the index `index` of Equation (2)'s family at which that very
member appears, with its base and its candidate identified. -/
structure AnchoredCertificatesWithExtra (data : GluingDatum target degree) (wall : target.V)
    {star : ThreeStar target wall} (input : W3SourceInput data star)
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
        extraFirst extraFirst_wall extraFirst_separate))) where
  /-- The incoming identification family's `t₄` member. -/
  positionMember : WallMember data wall input.distinguishedBlock.1
  /-- It isolates `t₄`. -/
  positionMember_isolated : positionMember.isolated = profile.largest.1.1.1
  /-- The anchored member is exactly the one named by `positionPlan`. -/
  positionMember_eq_plan : positionMember = positionPlan.member
    (SelectedSurvival.ofGrowProfile
      ((growProfileFirst profile directions largest_index).withExtra
        extraFirst extraFirst_wall extraFirst_separate))
    ((growProfileFirst profile directions largest_index).withExtra
      extraFirst extraFirst_wall extraFirst_separate).growAnchor_wall_rel
  /-- The literal Position I / Position II.b shape used for the anchored
  member.  Exposing it lets an incoming selected-block census be attached to
  the very member chosen by this certificate construction. -/
  positionMember_shape :
    (∃ hDisjoint : Disjoint
        ((data.edgePartition profile.first.1.1.1).block profile.first.1.1.2)
        ((data.edgePartition profile.second.1.1.1).block profile.second.1.1.2),
      positionMember = W3FourIncomingCensus.positionOneMember
        { toFourStarGeometry := ofGrowProfile
            ((growProfileFirst profile directions largest_index).withExtra
              extraFirst extraFirst_wall extraFirst_separate),
          disjoint := hDisjoint }
        (SelectedSurvival.ofGrowProfile
          ((growProfileFirst profile directions largest_index).withExtra
            extraFirst extraFirst_wall extraFirst_separate))
        input.distinguishedBlock.1
        ((growProfileFirst profile directions largest_index).withExtra
          extraFirst extraFirst_wall extraFirst_separate).growAnchor_wall_rel) ∨
    (∃ outside : Fin degree,
      ∃ hOutWall : (data.vertexPartition wall).Rel profile.first.1.1.2 outside,
      ∃ hOutGrow : ¬(data.edgePartition profile.first.1.1.1).Rel
        profile.first.1.1.2 outside,
      ∃ hOutOther : ¬(data.edgePartition profile.second.1.1.1).Rel
        profile.second.1.1.2 outside,
      positionMember = W3FourIncomingCensus.positionTwoMember
        { toFourStarGeometry := ofGrowProfile
            ((growProfileFirst profile directions largest_index).withExtra
              extraFirst extraFirst_wall extraFirst_separate),
          outside := outside, outside_wall := hOutWall,
          outside_grow := hOutGrow, outside_other := hOutOther }
        (SelectedSurvival.ofGrowProfile
          ((growProfileFirst profile directions largest_index).withExtra
            extraFirst extraFirst_wall extraFirst_separate))
        input.distinguishedBlock.1
        ((growProfileFirst profile directions largest_index).withExtra
          extraFirst extraFirst_wall extraFirst_separate).growAnchor_wall_rel)
  /-- Equation (2)'s four members, honest, with their dictionaries. -/
  certified : MemberCertificates data wall
    (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
      extraFirst extraFirst_wall extraFirst_separate))
  /-- Over the limit's own stable rows. -/
  rows_eq : certified.receipts.receipts.rows =
    limitRowsOfInput ((growProfileFirst profile directions largest_index).withExtra
      extraFirst extraFirst_wall extraFirst_separate)
  /-- `M⁽³⁾` lives over the incoming datum. -/
  base_three : certified.receipts.base 2 = data
  /-- and so does `M⁽⁴⁾`. -/
  base_four : certified.receipts.base 3 = data
  /-- `M⁽³⁾` is the case's own third candidate. -/
  candidate_three : HEq (certified.receipts.candidate 2)
    ((growProfileFirst profile directions largest_index).withExtra extraFirst
      extraFirst_wall extraFirst_separate).growCandidate
  /-- and `M⁽⁴⁾` its fourth. -/
  candidate_four : HEq (certified.receipts.candidate 3)
    ((growProfileSecond profile directions largest_index).withExtra extraSecond
      extraSecond_wall extraSecond_separate).growCandidate
  /-- The index of Equation (2)'s family carrying the incoming `t₄` member. -/
  index : Fin 4
  /-- It lives over the incoming datum, with no branch swap. -/
  base_index : certified.receipts.base index = data
  /-- and it **is** the incoming family's `t₄` member. -/
  candidate_index : HEq (certified.receipts.candidate index) positionMember.candidate

/-- **The anchored bundle exists**, on exactly the hypotheses
`W3FourRegrownColumnSeam.exists_memberCertificates` takes.

Under `Disjoint e₂ e₃` the incoming datum already carries Position I, so
`M⁽¹⁾` is built over it with `LimitChainCore.Gauge.refl` and only `M⁽²⁾` needs
`W3FourClosure.exists_member_two`'s branch-swapped copy; otherwise
`W3FourClosure.exists_outside_sheet` gives Position II.b over the incoming
datum and only `M⁽¹⁾` needs `exists_member_one`'s.  Either way the incoming
family's `t₄` member (`W3FourIncomingCensus.positionOneMember` or
`positionTwoMember` on the same `PositionOne`/`PositionTwo` data) is literally
a member of Equation (2)'s family. -/
theorem exists_anchoredCertificates_withExtra (hValid : data.Valid)
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
    Nonempty (AnchoredCertificatesWithExtra data wall input profile directions largest_index
      extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
      extraSecond_separate positionPlan) := by
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
        candidate_index := HEq.rfl }⟩
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
        candidate_index := HEq.rfl }⟩
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

/-- The canonical Position I / Position II.b anchoring plan. -/
noncomputable def defaultPositionPlan (data : GluingDatum target degree) (wall : target.V)
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    PositionPlan data wall
      (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
        (growProfileFirst profile directions largest_index).extraSheet
        (growProfileFirst profile directions largest_index).extraSheet_wall_rel
        (growProfileFirst profile directions largest_index).extraSheet_separate)) := by
  classical
  let grown := growProfileFirst profile directions largest_index
  rw [grown.withExtra_self]
  exact if hDisjoint : Disjoint
      ((data.edgePartition (ofGrowProfile grown).growTarget).block
        (ofGrowProfile grown).growAnchor)
      ((data.edgePartition (ofGrowProfile grown).otherTarget).block
        (ofGrowProfile grown).otherAnchor) then
    PositionPlan.one hDisjoint
  else
    let witness := W3FourClosure.exists_outside_sheet (ofGrowProfile grown) hDisjoint
    PositionPlan.two witness.choose witness.choose_spec.1 witness.choose_spec.2.1
      witness.choose_spec.2.2

/-- The original anchored bundle, using the canonical grow profiles' retained
transferred sheets. -/
abbrev AnchoredCertificates (data : GluingDatum target degree) (wall : target.V)
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :=
  AnchoredCertificatesWithExtra data wall input profile directions largest_index
    (growProfileFirst profile directions largest_index).extraSheet
    (growProfileFirst profile directions largest_index).extraSheet_wall_rel
    (growProfileFirst profile directions largest_index).extraSheet_separate
    (growProfileSecond profile directions largest_index).extraSheet
    (growProfileSecond profile directions largest_index).extraSheet_wall_rel
    (growProfileSecond profile directions largest_index).extraSheet_separate
    (defaultPositionPlan data wall input profile directions largest_index)

/-- The original anchored-certificate theorem, preserving its statement. -/
theorem exists_anchoredCertificates (hValid : data.Valid)
    (profile : Nd3Profile data input.distinguishedBlock)
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
    Nonempty (AnchoredCertificates data wall input profile directions largest_index) := by
  classical
  let positionPlan := defaultPositionPlan data wall input profile directions largest_index
  exact exists_anchoredCertificates_withExtra hValid profile directions largest_index
    (growProfileFirst profile directions largest_index).extraSheet
    (growProfileFirst profile directions largest_index).extraSheet_wall_rel
    (growProfileFirst profile directions largest_index).extraSheet_separate
    (growProfileSecond profile directions largest_index).extraSheet
    (growProfileSecond profile directions largest_index).extraSheet_wall_rel
    (growProfileSecond profile directions largest_index).extraSheet_separate
    positionPlan root hRoot hGrowFixed hLargestFixed hOtherMoved

end Anchored

/-! ## §2  `FamilyMatching`, inhabited -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
  (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
  (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      input.distinguishedBlock.1)
  (ac : AnchoredCertificates (contractDatum data hc hab hOne) ⟨a, hab⟩ input profile
    directions largest_index)

/-- **Family matching, proved.**  `W3FourHonestReceipts.FamilyMatching`
for the identification family built on the anchored bundle's own `t₄` member.

All three indices go through `W3FourHonestReceipts.exists_transported`, whose
whole proof is `subst`: at `1` and `2` on the bundle's `base_three`/`base_four`
and `candidate_three`/`candidate_four` (those are `W3FourIncomingMatching.figure28Members`'
Position II.a members, `W3FourSourceCandidates.thirdCandidate` and
`fourthCandidate` by `rfl`), and at `0` -- the `t₄` index -- on the
bundle's `base_index` and `candidate_index`.  No presentation is transported and
no branch swap is crossed: the bundle put the incoming `t₄` member into
Equation (2)'s family at construction time. -/
theorem familyMatching :
    W3FourHonestReceipts.FamilyMatching data hc hab hOne fullDim star input
      (figure28Members profile directions largest_index ac.positionMember)
      ac.certified :=
  W3FourHonestReceipts.familyMatching_of_position data hc hab hOne fullDim star input
    (figure28Members profile directions largest_index ac.positionMember) ac.certified
    ac.base_three ac.candidate_three ac.base_four ac.candidate_four
    (fun fd hMatrix hWall ↦ ⟨ac.index,
      W3FourHonestReceipts.exists_transported data hc hab hOne fullDim star input
        (figure28Members profile directions largest_index ac.positionMember)
        (ac.certified.receipts.candidate ac.index) 0 ac.base_index ac.candidate_index
        fd hMatrix hWall⟩)

/-- Family matching for a Figure 28 family whose two Position II.a members
carry prescribed transferred sheets. -/
theorem familyMatching_withExtra
    (extraFirst : Fin degree)
    (extraFirst_wall : ((contractDatum data hc hab hOne).vertexPartition
      ⟨a, hab⟩).Rel input.distinguishedBlock.1 extraFirst)
    (extraFirst_separate : ¬((contractDatum data hc hab hOne).edgePartition
      profile.first.1.1.1).Rel profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : ((contractDatum data hc hab hOne).vertexPartition
      ⟨a, hab⟩).Rel input.distinguishedBlock.1 extraSecond)
    (extraSecond_separate : ¬((contractDatum data hc hab hOne).edgePartition
      profile.second.1.1.1).Rel profile.second.1.1.2 extraSecond)
    (positionPlan : PositionPlan (contractDatum data hc hab hOne) ⟨a, hab⟩
      (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
        extraFirst extraFirst_wall extraFirst_separate)))
    (acExtra : AnchoredCertificatesWithExtra (contractDatum data hc hab hOne)
      ⟨a, hab⟩ input profile directions largest_index extraFirst extraFirst_wall
      extraFirst_separate extraSecond extraSecond_wall extraSecond_separate positionPlan) :
    W3FourHonestReceipts.FamilyMatching data hc hab hOne fullDim star input
      (W3FourIncomingMatching.figure28MembersWithExtra profile directions largest_index
        extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
        extraSecond_separate acExtra.positionMember)
      acExtra.certified :=
  W3FourHonestReceipts.familyMatching_of_position data hc hab hOne fullDim star input
    (W3FourIncomingMatching.figure28MembersWithExtra profile directions largest_index
      extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
      extraSecond_separate acExtra.positionMember) acExtra.certified
    acExtra.base_three acExtra.candidate_three acExtra.base_four acExtra.candidate_four
    (fun fd hMatrix hWall ↦ ⟨acExtra.index,
      W3FourHonestReceipts.exists_transported data hc hab hOne fullDim star input
        (W3FourIncomingMatching.figure28MembersWithExtra profile directions largest_index
          extraFirst extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate acExtra.positionMember)
        (acExtra.certified.receipts.candidate acExtra.index) 0 acExtra.base_index
        acExtra.candidate_index fd hMatrix hWall⟩)

end Matching

end DraismaVargas.LocalCases.W3FourFamilyMatching
