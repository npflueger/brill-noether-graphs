import DraismaVargas.LocalCases.W3TrackedAnchoring

/-!
# Source census anchoring with literal Figure 28 row dictionaries
This reconstructs the existing finite incoming census branching and calls the
stronger concrete anchored producer. No compatibility premise is added.
-/

namespace DraismaVargas.LocalCases.W3TrackedCensus

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


open W3FourClosureFinal W3TrackedAnchoring W4StableSource
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
theorem exists_tracked_censusAnchoring
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
    ∃ anchoring : CensusAnchoring data hc hab hOne fullDim star input profile directions
      largest_index,
      NaturalRowsCompatible anchoring.anchored.certified
        (StablePathLabelling.ofCardEq _ input.stablePath_card) := by
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
    obtain ⟨ac, hRows⟩ := exists_tracked_anchoredCertificates_withExtra
      input.valid profile directions largest_index y hyWall hySep second.extraSheet
      second.extraSheet_wall_rel second.extraSheet_separate plan treeRoot hTreeRoot hGrowFixed
      hLargestFixed hOtherMoved
    refine ⟨⟨y, hyWall, hySep, second.extraSheet, second.extraSheet_wall_rel,
      second.extraSheet_separate, plan, ac, ?_⟩, hRows⟩
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
    obtain ⟨ac, hRows⟩ := exists_tracked_anchoredCertificates_withExtra
      input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
      first.extraSheet_separate y hyWall hySep plan treeRoot hTreeRoot hGrowFixed
      hLargestFixed hOtherMoved
    refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
      y, hyWall, hySep, plan, ac, ?_⟩, hRows⟩
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
      obtain ⟨ac, hRows⟩ := exists_tracked_anchoredCertificates_withExtra
        input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
        first.extraSheet_separate second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
        plan treeRoot hTreeRoot hGrowFixed hLargestFixed hOtherMoved
      refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
        second.extraSheet, second.extraSheet_wall_rel, second.extraSheet_separate, plan, ac, ?_⟩, hRows⟩
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
      obtain ⟨ac, hRows⟩ := exists_tracked_anchoredCertificates_withExtra
        input.valid profile directions largest_index first.extraSheet first.extraSheet_wall_rel
        first.extraSheet_separate second.extraSheet second.extraSheet_wall_rel second.extraSheet_separate
        plan treeRoot hTreeRoot hGrowFixed hLargestFixed hOtherMoved
      refine ⟨⟨first.extraSheet, first.extraSheet_wall_rel, first.extraSheet_separate,
        second.extraSheet, second.extraSheet_wall_rel, second.extraSheet_separate, plan, ac, ?_⟩, hRows⟩
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
end DraismaVargas.LocalCases.W3TrackedCensus
