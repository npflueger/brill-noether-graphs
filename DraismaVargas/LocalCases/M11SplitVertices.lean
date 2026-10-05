module

public import DraismaVargas.LocalCases.M11SplitBranch
public import DraismaVargas.LocalCases.ResolutionStableIncidence

@[expose] public section

/-!
# Branch-vertex equivalence for the actual first M11 split

The distinguished old wall block maps to the unique new fresh branch vertex.
Every old branch away from the wall maps to its literal retained vertex.  The
left endpoint and all other fresh fibres contain no additional branch, so this
map exhausts the new branch vertices.
-/

namespace DraismaVargas.LocalCases.M11SplitVertices

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitBranch
open ResolutionAwayFromWall ResolutionStableIncidence StableGraphIncidence

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

include input profile

/-- The distinguished old wall block is the only incoming branch above the
wall. -/
theorem oldBranch_eq_selected (vertex : BranchVertex data)
    (hAt : vertex.1.1.1 = wall) :
    vertex.1 = WallBlock.sourceVertex data wall block := by
  by_contra hNe
  have hBackground : ¬ (data.vertexPartition wall).Rel block.1 vertex.1.1.2 := by
    intro hRel
    apply hNe
    exact ((data.sourceEndpoint_eq_iff wall block.1 vertex.1).mpr ⟨hAt.symm, hRel⟩).symm
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data
    (data.sourceEndpoint wall vertex.1.1.2)
  rw [M11JoinedDescentGeometry.background_old_card_incident input profile
    vertex.1.1.2 hBackground] at hUpper
  have hVertex := data.sourceEndpoint_self vertex.1
  rw [hAt] at hVertex
  rw [hVertex] at hUpper
  have hLower : 3 ≤ nonDanglingValency data vertex.1 := vertex.2
  omega

/-- The distinguished incoming branch as a branch-vertex object. -/
noncomputable def selectedOldBranch : BranchVertex data :=
  ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩

/-- The distinguished fresh branch as a branch-vertex object. -/
noncomputable def selectedNewBranch :
    BranchVertex (firstSplitPattern input profile hCard).candidate.datum :=
  ⟨branchVertex input profile hCard,
    (nonDanglingValency_branchVertex input profile hCard).ge⟩

/-- Retain an incoming branch known to lie away from the wall. -/
noncomputable def retainedBranch (vertex : BranchVertex data)
    (hAway : vertex.1.1.1 ≠ wall) :
    BranchVertex (firstSplitPattern input profile hCard).candidate.datum :=
  ⟨retainedVertex (firstSplitPattern input profile hCard).candidate vertex.1, by
    rw [nonDanglingValency_retainedVertex _ input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) vertex.1 hAway]
    exact vertex.2⟩

/-- Map an incoming branch to the actual first-split branch above the wall,
or to its retained copy away from the wall. -/
noncomputable def branchVertexMap :
    BranchVertex data →
      BranchVertex (firstSplitPattern input profile hCard).candidate.datum := fun vertex ↦ by
  if hAt : vertex.1.1.1 = wall then
    exact selectedNewBranch input profile hCard
  else
    exact retainedBranch input profile hCard vertex hAt

theorem branchVertexMap_of_wall (vertex : BranchVertex data)
    (hAt : vertex.1.1.1 = wall) :
    branchVertexMap input profile hCard vertex =
      selectedNewBranch input profile hCard := by
  unfold branchVertexMap
  exact dite_eq_left hAt

theorem branchVertexMap_of_away (vertex : BranchVertex data)
    (hAway : vertex.1.1.1 ≠ wall) :
    (branchVertexMap input profile hCard vertex).1 =
      retainedVertex (firstSplitPattern input profile hCard).candidate vertex.1 := by
  unfold branchVertexMap
  exact congrArg Subtype.val (dite_eq_right hAway)

theorem branchVertexMap_injective :
    Function.Injective (branchVertexMap input profile hCard) := by
  intro first second hEqual
  let candidate := (firstSplitPattern input profile hCard).candidate
  by_cases hFirst : first.1.1.1 = wall
  · by_cases hSecond : second.1.1.1 = wall
    · apply Subtype.ext
      exact (oldBranch_eq_selected input profile first hFirst).trans
        (oldBranch_eq_selected input profile second hSecond).symm
    · have hFirstMap := congrArg Subtype.val
        (branchVertexMap_of_wall input profile hCard first hFirst)
      have hSecondMap := branchVertexMap_of_away input profile hCard second hSecond
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
  · by_cases hSecond : second.1.1.1 = wall
    · have hFirstMap := branchVertexMap_of_away input profile hCard first hFirst
      have hSecondMap := congrArg Subtype.val
        (branchVertexMap_of_wall input profile hCard second hSecond)
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
    · apply Subtype.ext
      apply retainedVertex_injective_away candidate first.1 second.1 hFirst hSecond
      have hFirstMap := branchVertexMap_of_away input profile hCard first hFirst
      have hSecondMap := branchVertexMap_of_away input profile hCard second hSecond
      exact hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)

theorem branchVertexMap_surjective :
    Function.Surjective (branchVertexMap input profile hCard) := by
  intro vertex
  let candidate := (firstSplitPattern input profile hCard).candidate
  cases hPlace : vertex.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hVertex := candidate.datum.sourceEndpoint_self vertex.1
        rw [hPlace] at hVertex
        have hLe := left_valency_le_two input profile hCard vertex.1.1.2
        change nonDanglingValency candidate.datum
          (candidate.datum.sourceEndpoint (Sum.inl wall) vertex.1.1.2) ≤ 2 at hLe
        rw [hVertex] at hLe
        have hGe : 3 ≤ nonDanglingValency candidate.datum vertex.1 := vertex.2
        omega
      · obtain ⟨old, hOldTarget, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hPlace
        have hOldAway : old.1.1 ≠ wall := by
          intro hOldWall
          exact hAt (hOldTarget.symm.trans hOldWall)
        have hValency := nonDanglingValency_retainedVertex candidate input.valid
          (M11SourceGenus.firstSplit_sourceGenus input profile hCard) old hOldAway
        rw [hRetained] at hValency
        have hNewBranch : 3 ≤ nonDanglingValency candidate.datum vertex.1 := vertex.2
        have hOldBranch : 3 ≤ nonDanglingValency data old := by omega
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        exact (branchVertexMap_of_away input profile hCard oldBranch hOldAway).trans hRetained
  | inr point =>
      cases point
      have hVertex := candidate.datum.sourceEndpoint_self vertex.1
      rw [hPlace] at hVertex
      have hBranch : 3 ≤ nonDanglingValency candidate.datum
          (candidate.datum.sourceEndpoint (Sum.inr PUnit.unit) vertex.1.1.2) := by
        rw [hVertex]
        exact vertex.2
      have hSheet := (fresh_branch_iff input profile hCard vertex.1.1.2).mp hBranch
      let oldBranch : BranchVertex data :=
        ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩
      refine ⟨oldBranch, ?_⟩
      apply Subtype.ext
      have hMap := congrArg Subtype.val
        (branchVertexMap_of_wall input profile hCard oldBranch rfl)
      rw [hMap]
      change branchVertex input profile hCard = vertex.1
      rw [← hVertex, hSheet]
      rfl

/-- The actual branch-vertex bijection for the first split. -/
noncomputable def branchVertexEquiv :
    BranchVertex data ≃
      BranchVertex (firstSplitPattern input profile hCard).candidate.datum :=
  Equiv.ofBijective (branchVertexMap input profile hCard)
    ⟨branchVertexMap_injective input profile hCard,
      branchVertexMap_surjective input profile hCard⟩

@[simp] theorem branchVertexEquiv_apply (vertex : BranchVertex data) :
    branchVertexEquiv input profile hCard vertex =
      branchVertexMap input profile hCard vertex := rfl

/-- The selected incoming wall branch maps to the newly created fresh branch. -/
theorem branchVertexEquiv_selected :
    branchVertexEquiv input profile hCard
        ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩ =
      ⟨branchVertex input profile hCard,
        (nonDanglingValency_branchVertex input profile hCard).ge⟩ := by
  change branchVertexMap input profile hCard
      ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩ = _
  exact branchVertexMap_of_wall input profile hCard _ rfl

/-- Away from the wall, the branch equivalence is the literal retained-vertex
map used by the off-wall incidence theorem. -/
theorem branchVertexEquiv_away (vertex : BranchVertex data)
    (hAway : vertex.1.1.1 ≠ wall) :
    (branchVertexEquiv input profile hCard vertex).1 =
      retainedVertex (firstSplitPattern input profile hCard).candidate vertex.1 :=
  branchVertexMap_of_away input profile hCard vertex hAway

end DraismaVargas.LocalCases.M11SplitVertices
