module

public import DraismaVargas.LocalCases.W3FourFamilyMatching
public import DraismaVargas.LocalCases.W3FourSelectedCensus
public import DraismaVargas.Infrastructure.TargetSeparation

@[expose] public section

/-!
# The `w3Four` closure: the incoming sheet is the family sheet

Figure 28's Position II.a cover carries an actual transferred sheet.  This
module installs that sheet in `GrowProfile.withExtra`, builds Equation (2)'s
honest anchored family with those prescribed profiles, and supplies the
selected-block census to the original-coordinate positive-exit argument.
-/

namespace DraismaVargas.LocalCases.W3FourClosureFinal

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open FullDimensionalSource WallDegeneration W3R1SourceProfile
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond)
open W3FourClosure (ofGrowProfile)
open W3FourIncomingCensus (WallMember)
open W3FourIncomingMatching (figure28MembersWithExtra)
open W3ShiftIncomingMatching (SelectedCensus)
open W3FourFamilyMatching (PositionPlan AnchoredCertificatesWithExtra)
open W3FourRegrownColumnSeam (MemberCertificates)

/-- A default exact Position I / Position II.b plan for a fixed geometry. -/
noncomputable def somePositionPlan {target : CFGraph} {degree : ℕ}
    {wall : target.V} {data : GluingDatum target degree}
    (geometry : W3FourClosure.FourStarGeometry data wall) :
    PositionPlan data wall geometry := by
  classical
  exact if hDisjoint : Disjoint
      ((data.edgePartition geometry.growTarget).block geometry.growAnchor)
      ((data.edgePartition geometry.otherTarget).block geometry.otherAnchor) then
    PositionPlan.one hDisjoint
  else
    let witness := W3FourClosure.exists_outside_sheet geometry hDisjoint
    PositionPlan.two witness.choose witness.choose_spec.1 witness.choose_spec.2.1
      witness.choose_spec.2.2

/-- The Figure 28 family after installing the incoming Position II.a sheet.
The position member is likewise fixed by the incoming Position I/II.b census,
so the selected partitions below refer literally to the certified family. -/
structure CensusAnchoring {target : CFGraph} {degree : ℕ} {a b : target.V}
    {contracted : target.edges} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) where
  extraFirst : Fin degree
  extraFirst_wall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
    input.distinguishedBlock.1 extraFirst
  extraFirst_separate : ¬((contractDatum data hc hab hOne).edgePartition
    profile.first.1.1.1).Rel profile.first.1.1.2 extraFirst
  extraSecond : Fin degree
  extraSecond_wall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
    input.distinguishedBlock.1 extraSecond
  extraSecond_separate : ¬((contractDatum data hc hab hOne).edgePartition
    profile.second.1.1.1).Rel profile.second.1.1.2 extraSecond
  positionPlan : PositionPlan (contractDatum data hc hab hOne) ⟨a, hab⟩
    (ofGrowProfile ((growProfileFirst profile directions largest_index).withExtra
      extraFirst extraFirst_wall extraFirst_separate))
  anchored : AnchoredCertificatesWithExtra (contractDatum data hc hab hOne) ⟨a, hab⟩
    input profile directions largest_index extraFirst extraFirst_wall extraFirst_separate
    extraSecond extraSecond_wall extraSecond_separate positionPlan
  census : ∀ index : Fin 3,
    divalentOccurrence data hc hab hOne fullDim star =
        (figure28MembersWithExtra profile directions largest_index extraFirst
          extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate anchored.positionMember index).isolated →
      SelectedCensus data hc hab hOne star input
        (figure28MembersWithExtra profile directions largest_index extraFirst
          extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate anchored.positionMember index).selectedLeft
        (figure28MembersWithExtra profile directions largest_index extraFirst
          extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate anchored.positionMember index).selectedRight
        (figure28MembersWithExtra profile directions largest_index extraFirst
          extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate anchored.positionMember index).selectedNew

section CensusAnchoring

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
  (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
  (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      input.distinguishedBlock.1)

include fullDim hForest hCompat

/-- The incoming cover supplies all sheet choices and the exact position
member needed to anchor the certified Figure 28 family. -/
theorem exists_censusAnchoring
    (treeRoot : (contract target hab hOne).V) (hTreeRoot : treeRoot ≠ ⟨a, hab⟩)
    (hGrowFixed : TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V)
      treeRoot hTreeRoot
      profile.first.1.1.1 = false)
    (hLargestFixed : TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V)
      treeRoot hTreeRoot
      profile.largest.1.1.1 = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V)
      treeRoot hTreeRoot
      profile.second.1.1.1 = true) :
    Nonempty (CensusAnchoring data hc hab hOne fullDim star input profile directions
      largest_index) := by
  classical
  let first := growProfileFirst profile directions largest_index
  let second := growProfileSecond profile directions largest_index
  rcases W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest data hc hab
      hOne fullDim hForest hCompat star input profile directions largest_index with
    hFirst | hSecond | hLargest
  · obtain ⟨y, hySep, hyWall, hyCensus⟩ := W3FourSelectedCensus.classes_of_grow data
      hc hab hOne fullDim hForest hCompat star input first hFirst
    let first' := first.withExtra y hyWall hySep
    let plan := somePositionPlan (ofGrowProfile first')
    obtain ⟨ac⟩ := W3FourFamilyMatching.exists_anchoredCertificates_withExtra
      input.valid profile directions largest_index y hyWall hySep second.extraSheet
      second.extraSheet_wall_rel second.extraSheet_separate plan treeRoot hTreeRoot hGrowFixed
      hLargestFixed hOtherMoved
    refine ⟨⟨y, hyWall, hySep, second.extraSheet, second.extraSheet_wall_rel,
      second.extraSheet_separate, plan, ac, ?_⟩⟩
    intro index hIndex
    fin_cases index
    · exact absurd (hFirst.symm.trans (hIndex.trans ac.positionMember_isolated))
        profile.first_target_ne
    · change SelectedCensus data hc hab hOne star input first'.growPartition
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        first'.growPartition
      exact hyCensus
    · exact absurd (hFirst.symm.trans hIndex) directions
  · obtain ⟨y, hySep, hyWall, hyCensus⟩ := W3FourSelectedCensus.classes_of_grow data
      hc hab hOne fullDim hForest hCompat star input second hSecond
    let second' := second.withExtra y hyWall hySep
    let first' := first.withExtra first.extraSheet first.extraSheet_wall_rel first.extraSheet_separate
    let plan := somePositionPlan (ofGrowProfile first')
    obtain ⟨ac⟩ := W3FourFamilyMatching.exists_anchoredCertificates_withExtra
      input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
      first.extraSheet_separate y hyWall hySep plan treeRoot hTreeRoot hGrowFixed
      hLargestFixed hOtherMoved
    refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
      y, hyWall, hySep, plan, ac, ?_⟩⟩
    intro index hIndex
    fin_cases index
    · exact absurd (hSecond.symm.trans (hIndex.trans ac.positionMember_isolated))
        profile.second_target_ne
    · exact absurd (hSecond.symm.trans hIndex).symm directions
    · change SelectedCensus data hc hab hOne star input second'.growPartition
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        second'.growPartition
      exact hyCensus
  · rcases W3FourSelectedCensus.classes_of_largest data hc hab hOne fullDim hForest
        hCompat star input first hLargest with
      ⟨hDisjoint, hCensus⟩ | ⟨x, hxWall, hxGrow, hxOther, hCensus⟩
    · let first' := first.withExtra first.extraSheet first.extraSheet_wall_rel
          first.extraSheet_separate
      have hfirst' : first' = first := by
        exact GrowProfile.withExtra_self first
      have hDisjoint' : Disjoint
          (((contractDatum data hc hab hOne).edgePartition first'.growTarget).block
            first'.growAnchor)
          (((contractDatum data hc hab hOne).edgePartition first'.otherTarget).block
            first'.otherAnchor) := by rw [hfirst']; exact hDisjoint
      let plan : PositionPlan (contractDatum data hc hab hOne) ⟨a, hab⟩
          (ofGrowProfile first') := .one hDisjoint'
      obtain ⟨ac⟩ := W3FourFamilyMatching.exists_anchoredCertificates_withExtra
        input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
        first.extraSheet_separate second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
        plan treeRoot hTreeRoot hGrowFixed hLargestFixed hOtherMoved
      refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
        second.extraSheet, second.extraSheet_wall_rel, second.extraSheet_separate, plan, ac, ?_⟩⟩
      intro index hIndex
      fin_cases index
      · rw [ac.positionMember_eq_plan]
        convert hCensus using 1
        <;> simp [figure28MembersWithExtra, plan, PositionPlan.member,
          W3FourIncomingCensus.positionOneMember, first]
        <;> congr 1
      · exact absurd (hLargest.symm.trans hIndex) (Ne.symm profile.first_target_ne)
      · exact absurd (hLargest.symm.trans hIndex) (Ne.symm profile.second_target_ne)
    · let first' := first.withExtra first.extraSheet first.extraSheet_wall_rel
          first.extraSheet_separate
      have hfirst' : first' = first := by
        exact GrowProfile.withExtra_self first
      have hxWall' : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          first'.growAnchor x := by rw [hfirst']; exact hxWall
      have hxGrow' : ¬((contractDatum data hc hab hOne).edgePartition
          first'.growTarget).Rel first'.growAnchor x := by rw [hfirst']; exact hxGrow
      have hxOther' : ¬((contractDatum data hc hab hOne).edgePartition
          first'.otherTarget).Rel first'.otherAnchor x := by rw [hfirst']; exact hxOther
      let plan : PositionPlan (contractDatum data hc hab hOne) ⟨a, hab⟩
          (ofGrowProfile first') := .two x hxWall' hxGrow' hxOther'
      obtain ⟨ac⟩ := W3FourFamilyMatching.exists_anchoredCertificates_withExtra
        input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
        first.extraSheet_separate second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
        plan treeRoot hTreeRoot hGrowFixed hLargestFixed hOtherMoved
      refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
        second.extraSheet, second.extraSheet_wall_rel, second.extraSheet_separate, plan, ac, ?_⟩⟩
      intro index hIndex
      fin_cases index
      · rw [ac.positionMember_eq_plan]
        convert hCensus using 1
        <;> simp [figure28MembersWithExtra, plan, PositionPlan.member,
          W3FourIncomingCensus.positionTwoMember, first]
        <;> congr 1
      · exact absurd (hLargest.symm.trans hIndex) (Ne.symm profile.first_target_ne)
      · exact absurd (hLargest.symm.trans hIndex) (Ne.symm profile.second_target_ne)

end CensusAnchoring

section Final

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
  (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
  (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
      input.distinguishedBlock.1)

/-- The full original-coordinate exit attached to a census anchoring.  This
proposition is an output format; the anchoring itself is constructed by
`exists_censusAnchoring` rather than asked of a caller. -/
def PositiveExitOfAnchoring
    (anchoring : CensusAnchoring data hc hab hOne fullDim star input profile directions
      largest_index)
    (_root : (contract target hab hOne).V)
    (z incomingVelocity : coordinate → ℚ) : Prop :=
  let ac := anchoring.anchored
  let members := figure28MembersWithExtra profile directions largest_index
    anchoring.extraFirst anchoring.extraFirst_wall anchoring.extraFirst_separate
    anchoring.extraSecond anchoring.extraSecond_wall anchoring.extraSecond_separate
    ac.positionMember
  ∃ index : Fin 3,
    divalentOccurrence data hc hab hOne fullDim star = (members index).isolated ∧
    Nonempty (StableGraphIncidence.Equivalence data (members index).candidate.datum) ∧
    ∃ incoming : Fin 4,
      ∃ incomingFD : FullDimensionalSourcePresentation
          (ac.certified.receipts.candidate incoming).datum coordinate,
      ∃ outgoing : Fin 4,
        (ac.certified.receipts.candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            fullDim.labelling.presentation).det *
          (W3FourHonestReceipts.squareMatrix ac.certified incoming
            incomingFD.labelling outgoing).det < 0 ∧
        (∃ outgoingFD : FullDimensionalSourcePresentation
            (ac.certified.receipts.candidate outgoing).datum coordinate,
          outgoingFD.labelling =
            W3FourHonestReceipts.labelling ac.certified incoming
              incomingFD.labelling outgoing ∧
          Nonempty (StableGraphIncidence.Equivalence data
            (ac.certified.receipts.candidate outgoing).datum)) ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧
          ∀ t : ℚ, 0 < t → t ≤ δ →
            (∀ i, 0 < (z + t • velocity) i) ∧
            (W3FourHonestReceipts.squareMatrix ac.certified incoming
                incomingFD.labelling outgoing).mulVec (z + t • velocity) =
              (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec z +
                t • (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec incomingVelocity ∧
            ∃ realization :
                (ac.certified.receipts.candidate outgoing).datum.IntegralRealization,
              ∃ scale : ℕ, 0 < scale ∧
                (∀ column,
                  (realization.targetLength
                    ((W3FourHonestReceipts.labelling ac.certified incoming
                      incomingFD.labelling outgoing).targetEdge column) : ℚ) =
                    (scale : ℚ) * (z + t • velocity) column) ∧
                Utilities.BNExists realization.sourceSpec.graph 1 degree

include hForest hCompat

end Final

end DraismaVargas.LocalCases.W3FourClosureFinal
