module

public import DraismaVargas.LocalCases.M11JoinedRowDescent

@[expose] public section

/-!
# The actual joined M11 branch endpoint

At the endpoint selected by `SourceProfile.doubleLabel`, the two retained
double-direction occurrences and the distinguished new joined occurrence are
exactly the surviving incidences.  We retain the three occurrences separately:
their stable classes need not be distinct.
-/

namespace DraismaVargas.LocalCases.M11JoinedBranch

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11JoinedGeometry M11JoinedSurvival
open M11JoinedDescentGeometry M11JoinedRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The actual selected double-direction endpoint in the joined candidate. -/
noncomputable def branchVertex {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (joinedPattern data star block hCard).candidate.datum.SourceVertex :=
  (joinedPattern data star block hCard).candidate.datum.sourceEndpoint
    (endpoint target wall profile.doubleLabel) block.1

/-- The first retained occurrence ending at the joined branch vertex. -/
noncomputable def firstEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (joinedPattern data star block hCard).candidate.datum :=
  ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge profile.first.1,
    ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      profile.first_survives⟩

/-- The second retained occurrence ending at the joined branch vertex. -/
noncomputable def secondEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (joinedPattern data star block hCard).candidate.datum :=
  ⟨(joinedPattern data star block hCard).candidate.oldSourceEdge profile.second.1,
    ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      profile.second_survives⟩

/-- The distinguished new joined occurrence ending at the branch vertex. -/
noncomputable def thirdEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (joinedPattern data star block hCard).candidate.datum :=
  ⟨(joinedPattern data star block hCard).candidate.newSourceEdge block.1,
    joined_distinguished_survives input profile hCard⟩

theorem firstEnd_incident (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      (firstEnd input profile hCard).1 (branchVertex profile hCard) :=
  oldSourceEdge_incident_of_target_rel data star block hCard _ _
    profile.first_target _ (M11SplitSurvival.sheet_rel_of_incident_block profile.first)

theorem secondEnd_incident (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      (secondEnd input profile hCard).1 (branchVertex profile hCard) :=
  oldSourceEdge_incident_of_target_rel data star block hCard _ _
    profile.second_target _ (M11SplitSurvival.sheet_rel_of_incident_block profile.second)

theorem thirdEnd_incident (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (joinedPattern data star block hCard).candidate.datum
      (thirdEnd input profile hCard).1 (branchVertex profile hCard) :=
  newSourceEdge_incident_endpoint data star block hCard _ _

theorem firstEnd_ne_secondEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    firstEnd input profile hCard ≠ secondEnd input profile hCard := by
  intro h
  apply profile.first_ne_second
  apply Subtype.ext
  exact ResolutionCut.oldSourceEdge_injective _ (congrArg Subtype.val h)

theorem oldEnd_ne_thirdEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (old : data.SourceEdge) :
    (joinedPattern data star block hCard).candidate.oldSourceEdge old ≠
      (thirdEnd input profile hCard).1 := by
  intro h
  have hLabels := (occurrenceEquiv target wall
      (joinedPattern data star block hCard).candidate.right).injective
    (congrArg (fun edge : (joinedPattern data star block hCard).candidate.datum.SourceEdge ↦
      edge.1.1) h)
  cases hLabels

/-- The exact surviving incidence set at the selected joined branch endpoint. -/
theorem nonDanglingIncident_branchVertex (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    nonDanglingIncident (joinedPattern data star block hCard).candidate.datum
        (branchVertex profile hCard) =
      {(firstEnd input profile hCard).1, (secondEnd input profile hCard).1,
        (thirdEnd input profile hCard).1} := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  let vertex := branchVertex profile hCard
  let first := firstEnd input profile hCard
  let second := secondEnd input profile hCard
  let third := thirdEnd input profile hCard
  have hFirst : first.1 ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨first.2, firstEnd_incident input profile hCard⟩
  have hSecond : second.1 ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨second.2, secondEnd_incident input profile hCard⟩
  have hThird : third.1 ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨third.2, thirdEnd_incident input profile hCard⟩
  have hSubset : ({first.1, second.1, third.1} : Finset candidate.datum.SourceEdge) ⊆
      nonDanglingIncident candidate.datum vertex := by
    intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact hFirst
    · exact hSecond
    · exact hThird
  have hFirstSecond : first.1 ≠ second.1 := by
    intro h
    exact firstEnd_ne_secondEnd input profile hCard (Subtype.ext h)
  have hFirstThird : first.1 ≠ third.1 :=
    oldEnd_ne_thirdEnd input profile hCard profile.first.1
  have hSecondThird : second.1 ≠ third.1 :=
    oldEnd_ne_thirdEnd input profile hCard profile.second.1
  apply Finset.Subset.antisymm _ hSubset
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
    candidate.datum vertex
  change nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall profile.doubleLabel) block.1) ≤
    Fintype.card (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (endpoint target wall profile.doubleLabel) block.1)) at hUpper
  rw [card_incident_distinguished_endpoint profile hCard profile.doubleLabel] at hUpper
  have hTripleCard : ({first.1, second.1, third.1} : Finset candidate.datum.SourceEdge).card = 3 := by
    simp [hFirstSecond, hFirstThird, hSecondThird]
  intro edge hEdge
  by_contra hNot
  have hStrict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hSubset, fun hEq ↦ hNot (hEq ▸ hEdge)⟩)
  rw [hTripleCard, card_nonDanglingIncident] at hStrict
  change 3 < nonDanglingValency candidate.datum
    (candidate.datum.sourceEndpoint (endpoint target wall profile.doubleLabel) block.1) at hStrict
  omega

/-- The selected joined endpoint is exactly trivalent after pruning. -/
theorem branchVertex_valency (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      (branchVertex profile hCard) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_branchVertex input profile hCard]
  have hFirstSecond : (firstEnd input profile hCard).1 ≠
      (secondEnd input profile hCard).1 := fun h ↦
    firstEnd_ne_secondEnd input profile hCard (Subtype.ext h)
  have hFirstThird : (firstEnd input profile hCard).1 ≠
      (thirdEnd input profile hCard).1 :=
    oldEnd_ne_thirdEnd input profile hCard profile.first.1
  have hSecondThird : (secondEnd input profile hCard).1 ≠
      (thirdEnd input profile hCard).1 :=
    oldEnd_ne_thirdEnd input profile hCard profile.second.1
  simp [hFirstSecond, hFirstThird, hSecondThird]

theorem firstEnd_isPathEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsPathEnd (joinedPattern data star block hCard).candidate.datum
      (firstEnd input profile hCard).1 (branchVertex profile hCard) :=
  ⟨firstEnd_incident input profile hCard, by rw [branchVertex_valency input profile hCard]; omega⟩

theorem secondEnd_isPathEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsPathEnd (joinedPattern data star block hCard).candidate.datum
      (secondEnd input profile hCard).1 (branchVertex profile hCard) :=
  ⟨secondEnd_incident input profile hCard, by rw [branchVertex_valency input profile hCard]; omega⟩

theorem thirdEnd_isPathEnd (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsPathEnd (joinedPattern data star block hCard).candidate.datum
      (thirdEnd input profile hCard).1 (branchVertex profile hCard) :=
  ⟨thirdEnd_incident input profile hCard, by rw [branchVertex_valency input profile hCard]; omega⟩

/-- The first branch flag carries the original first stable row. -/
theorem firstEnd_stablePath (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (firstEnd input profile hCard).stablePath =
      stablePathEquiv input profile hCard
        (NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩) := by
  let old : NonDanglingEdge data := ⟨profile.first.1, profile.first_survives⟩
  rw [show NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩ =
      old.stablePath from rfl,
    stablePathEquiv_mk input profile hCard old]
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext rfl)

/-- The second branch flag carries the original second stable row. -/
theorem secondEnd_stablePath (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (secondEnd input profile hCard).stablePath =
      stablePathEquiv input profile hCard
        (NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩) := by
  let old : NonDanglingEdge data := ⟨profile.second.1, profile.second_survives⟩
  rw [show NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩ =
      old.stablePath from rfl,
    stablePathEquiv_mk input profile hCard old]
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext rfl)

/-- The new joined branch flag carries the original third stable row. -/
theorem thirdEnd_stablePath (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (thirdEnd input profile hCard).stablePath =
      stablePathEquiv input profile hCard
        (NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩) := by
  let old : NonDanglingEdge data := ⟨profile.third.1, profile.third_survives⟩
  rw [show NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ =
      old.stablePath from rfl,
    stablePathEquiv_mk input profile hCard old]
  exact (joined_distinguished_stablePath_eq input profile hCard).trans
    (congrArg NonDanglingEdge.stablePath (Subtype.ext rfl))

end DraismaVargas.LocalCases.M11JoinedBranch
