module

public import DraismaVargas.LocalCases.W3Nd2FineRowDescent
public import DraismaVargas.LocalCases.ResolutionStableIncidence
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# Stable-incidence certificate for the true Figure 31 fine member

Old branches away from the resolved wall are retained.  Since the selected
old wall block is divalent, every old wall branch is a background block and
maps to the corresponding fresh endpoint.  The expanded left endpoints and
the selected fresh endpoints have surviving valency at most two: the anchor
is divalent and the distinct residual singleton has valency zero. Thus every
new branch is an actual old background branch.
-/

namespace DraismaVargas.LocalCases.W3Nd2FineStableGraph

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2EndRows W3Nd2Background
open W3Nd2StableLift W3Nd2FineRowDescent ResolutionM11 ResolutionPruning
open ResolutionSurvival ResolutionAwayFromWall ResolutionStableIncidence
open StableGraphIncidence StablePathCount NonDanglingValency
open M11SplitSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-- The selected fine left endpoint has exactly the anchor-new and retained
large survivors; the residual new occurrence supplies the deleted third
flag. -/
theorem fine_selected_left_valency_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) = 2 := by
  classical
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) (anchor input profile)
  change nonDanglingValency candidate.datum vertex = 2
  let dangling : IncidentSourceEdge candidate.datum vertex :=
    ⟨candidate.newSourceEdge (residualSheet input profile),
      fine_residual_new_incident_left input profile⟩
  have hDanglingPositive : 0 <
      ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
        (fun edge ↦ IsDangling candidate.datum edge.1)).card :=
    Finset.card_pos.mpr ⟨dangling, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fine_residual_new_dangles input profile⟩⟩
  have hSurvivingPositive :=
    ClassInjectivity.nonDanglingValency_ne_zero_of_incident candidate.datum
      (fine_anchor_new_survives input profile)
      (fine_anchor_new_incident_left input profile)
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one candidate.datum
    (fineCandidate_valid input profile).1 vertex
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    fine_left_card_three input profile] at hTotal
  dsimp only [candidate, vertex] at hDanglingPositive hSurvivingPositive hNotOne hTotal ⊢
  omega

/-- Every expanded old-wall endpoint of the fine candidate has surviving
valency at most two. -/
theorem fine_left_valency_le_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree) :
    nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2 := by
  by_cases hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet
  · have hEndpoint := fine_left_endpoint_eq_of_wall_rel input profile
      (anchor input profile) sheet (anchor_wall_rel input profile)
      ((anchor_wall_rel input profile).symm.trans hSelected)
    rw [← hEndpoint, fine_selected_left_valency_two input profile]
  · have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
      (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)
    rw [fine_background_left_card_two input profile sheet hSelected] at hUpper
    exact hUpper

theorem fine_fresh_endpoint_eq_of_fine_rel
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hFine : (finePartition input profile).Rel first second) :
    (fineCandidate input profile).datum.sourceEndpoint (freshVertex target) first =
      (fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile).right.repr first =
      (finePastedResolution input profile).right.repr second
    apply (finePastedResolution input profile).right.mem_block_iff _ _ |>.mp
    rw [pasted_right_block_selected input profile first hSelected]
    exact (finePartition input profile).mem_block_iff _ _ |>.mpr hFine

/-- Every occurrence at the residual selected fresh singleton dangles. -/
theorem fine_residual_fresh_valency_zero
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (residualSheet input profile)) = 0 := by
  classical
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (freshVertex target)
    (residualSheet input profile)
  let oldSmall : IncidentSourceEdge candidate.datum vertex :=
    ⟨candidate.oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile)), by
      apply oldSourceEdge_incident_fresh
      · exact smallTarget_mem input profile
      · change rightOf (largeTarget input profile) (smallTarget input profile) = true
        simp [rightOf, profile.target_ne]
      ⟩
  let oldThird : IncidentSourceEdge candidate.datum vertex :=
    ⟨candidate.oldSourceEdge (thirdSourceEdge input profile (residualSheet input profile)), by
      apply oldSourceEdge_incident_fresh
      · exact thirdTarget_mem input profile
      · change rightOf (largeTarget input profile) (thirdTarget input profile) = true
        simp [rightOf, thirdTarget_ne_large input profile]
      ⟩
  let newEdge : IncidentSourceEdge candidate.datum vertex :=
    ⟨candidate.newSourceEdge (residualSheet input profile), by
      exact Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
        candidate.right (finePastedResolution input profile)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior)
        (residualSheet input profile)))⟩
  have hSmallThird : oldSmall ≠ oldThird := by
    intro hEqual
    have hTargets := congrArg
      (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    exact thirdTarget_ne_small input profile (Option.some.inj hLabels).symm
  have hSmallNew : oldSmall ≠ newEdge := by
    intro hEqual
    have hTargets := congrArg
      (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  have hThirdNew : oldThird ≠ newEdge := by
    intro hEqual
    have hTargets := congrArg
      (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  have hSubset : ({oldSmall, oldThird, newEdge} :
      Finset (IncidentSourceEdge candidate.datum vertex)) ⊆
      (Finset.univ.filter fun edge : IncidentSourceEdge candidate.datum vertex ↦
        IsDangling candidate.datum edge.1) := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with hSmall | hRest
    · subst edge
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fine_residual_oldSmall_dangles input profile⟩
    · rcases Finset.mem_insert.mp hRest with hThird | hNew
      · subst edge
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fine_residual_oldThird_dangles input profile⟩
      · rw [Finset.mem_singleton] at hNew
        subst edge
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fine_residual_new_dangles input profile⟩
  have hThree : 3 ≤ ((Finset.univ : Finset
      (IncidentSourceEdge candidate.datum vertex)).filter fun edge ↦
        IsDangling candidate.datum edge.1).card := by
    have hCard : ({oldSmall, oldThird, newEdge} :
        Finset (IncidentSourceEdge candidate.datum vertex)).card = 3 := by
      simp [hSmallThird, hSmallNew, hThirdNew]
    rw [← hCard]
    exact Finset.card_le_card hSubset
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    fine_residual_right_card_three input profile] at hTotal
  dsimp only [candidate, vertex] at hThree hTotal ⊢
  omega

/-- A selected fine fresh endpoint is either the divalent anchor endpoint or
the zero-valent residual singleton endpoint. -/
theorem fine_fresh_selected_valency_le_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) ≤ 2 := by
  have hWallMem : sheet ∈ (data.vertexPartition wall).block (anchor input profile) :=
    (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((anchor_wall_rel input profile).symm.trans hSelected)
  rw [← fine_blocks_cover_wall input profile] at hWallMem
  rcases Finset.mem_union.mp hWallMem with hResidual | hAnchor
  · have hFine := (finePartition input profile).mem_block_iff _ _ |>.mp hResidual
    have hEndpoint := fine_fresh_endpoint_eq_of_fine_rel input profile
      (residualSheet input profile) sheet (residualSheet_wall_rel input profile) hFine
    rw [← hEndpoint, fine_residual_fresh_valency_zero input profile]
    omega
  · have hFine := (finePartition input profile).mem_block_iff _ _ |>.mp hAnchor
    have hEndpoint := fine_fresh_endpoint_eq_of_fine_rel input profile
      (anchor input profile) sheet (anchor_wall_rel input profile) hFine
    rw [← hEndpoint, fine_right_nonDanglingValency_eq_two input profile]

/-- An old branch above the wall cannot be the distinguished divalent block. -/
theorem old_wall_branch_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data)
    (hAt : vertex.1.1.1 = wall) :
    ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 vertex.1.1.2 := by
  intro hSelected
  have hVertex : vertex.1 = WallBlock.sourceVertex data wall input.distinguishedBlock :=
    ((data.sourceEndpoint_eq_iff wall input.distinguishedBlock.1 vertex.1).mpr
      ⟨hAt.symm, hSelected⟩).symm
  have hBranch : 3 ≤ nonDanglingValency data vertex.1 := vertex.2
  rw [hVertex, profile.valency] at hBranch
  omega

/-- A background branch above the old wall moves to the corresponding fresh
endpoint. -/
noncomputable def fineBackgroundFreshBranch
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data)
    (hAt : vertex.1.1.1 = wall) :
    BranchVertex (fineCandidate input profile).datum :=
  ⟨(fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
      vertex.1.1.2, by
    rw [fine_nonDanglingValency_background input profile vertex.1.1.2
      (old_wall_branch_background input profile vertex hAt)]
    have hSelf := data.sourceEndpoint_self vertex.1
    rw [hAt] at hSelf
    rw [hSelf]
    exact vertex.2⟩

/-- An old branch away from the wall is retained literally. -/
noncomputable def fineRetainedBranch
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data)
    (hAway : vertex.1.1.1 ≠ wall) :
    BranchVertex (fineCandidate input profile).datum :=
  ⟨retainedVertex (fineCandidate input profile) vertex.1, by
    rw [nonDanglingValency_retainedVertex _ input.valid
      (fineCandidate_sourceGenus input profile) vertex.1 hAway]
    exact vertex.2⟩

/-- The actual fine branch map: wall-background branches move to the fresh
side and all off-wall branches are retained. -/
noncomputable def fineBranchVertexMap
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BranchVertex data → BranchVertex (fineCandidate input profile).datum :=
  fun vertex ↦ if hAt : vertex.1.1.1 = wall then
    fineBackgroundFreshBranch input profile vertex hAt
  else fineRetainedBranch input profile vertex hAt

theorem fineBranchVertexMap_of_wall
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall) :
    (fineBranchVertexMap input profile vertex).1 =
      (fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        vertex.1.1.2 := by
  unfold fineBranchVertexMap
  exact congrArg Subtype.val (dite_eq_left hAt)

theorem fineBranchVertexMap_of_away
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    (fineBranchVertexMap input profile vertex).1 =
      retainedVertex (fineCandidate input profile) vertex.1 := by
  unfold fineBranchVertexMap
  exact congrArg Subtype.val (dite_eq_right hAway)

/-- On background blocks, equality of fresh endpoints reflects equality of
the corresponding old wall endpoints. -/
theorem fine_fresh_endpoint_reflects_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : Fin degree)
    (hFirst : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hEqual : (fineCandidate input profile).datum.sourceEndpoint
        (freshVertex target) first =
      (fineCandidate input profile).datum.sourceEndpoint
        (freshVertex target) second) :
    data.sourceEndpoint wall first = data.sourceEndpoint wall second := by
  have hRight : (finePastedResolution input profile).right.Rel first second := by
    change (finePastedResolution input profile).right.repr first =
      (finePastedResolution input profile).right.repr second
    exact congrArg (fun vertex : (fineCandidate input profile).datum.SourceVertex ↦
      vertex.1.2) hEqual
  have hWall : (data.vertexPartition wall).Rel first second := by
    apply (data.vertexPartition wall).mem_block_iff _ _ |>.mp
    rw [← fine_background_right_block input profile first hFirst,
      (finePastedResolution input profile).right.mem_block_iff]
    exact hRight
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hWall

/-- Replacing a background sheet by its old wall representative does not
change the corresponding fine fresh endpoint. -/
theorem fine_fresh_endpoint_wall_repr
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        ((data.vertexPartition wall).repr sheet) =
      (fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile).right.repr
      ((data.vertexPartition wall).repr sheet) =
        (finePastedResolution input profile).right.repr sheet
    symm
    apply (finePastedResolution input profile).right.mem_block_iff _ _ |>.mp
    rw [fine_background_right_block input profile sheet hBackground]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((data.vertexPartition wall).rel_repr_right sheet)

theorem fineBranchVertexMap_injective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Injective (fineBranchVertexMap input profile) := by
  intro first second hEqual
  let candidate := fineCandidate input profile
  by_cases hFirst : first.1.1.1 = wall
  · by_cases hSecond : second.1.1.1 = wall
    · apply Subtype.ext
      have hFirstMap := fineBranchVertexMap_of_wall input profile first hFirst
      have hSecondMap := fineBranchVertexMap_of_wall input profile second hSecond
      have hFresh := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hOld := fine_fresh_endpoint_reflects_background input profile
        first.1.1.2 second.1.1.2
        (old_wall_branch_background input profile first hFirst) hFresh
      have hFirstSelf := data.sourceEndpoint_self first.1
      have hSecondSelf := data.sourceEndpoint_self second.1
      rw [hFirst] at hFirstSelf
      rw [hSecond] at hSecondSelf
      exact hFirstSelf.symm.trans (hOld.trans hSecondSelf)
    · have hFirstMap := fineBranchVertexMap_of_wall input profile first hFirst
      have hSecondMap := fineBranchVertexMap_of_away input profile second hSecond
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
  · by_cases hSecond : second.1.1.1 = wall
    · have hFirstMap := fineBranchVertexMap_of_away input profile first hFirst
      have hSecondMap := fineBranchVertexMap_of_wall input profile second hSecond
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
    · apply Subtype.ext
      apply retainedVertex_injective_away candidate first.1 second.1 hFirst hSecond
      have hFirstMap := fineBranchVertexMap_of_away input profile first hFirst
      have hSecondMap := fineBranchVertexMap_of_away input profile second hSecond
      exact hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)

theorem fineBranchVertexMap_surjective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Surjective (fineBranchVertexMap input profile) := by
  intro vertex
  let candidate := fineCandidate input profile
  cases hPlace : vertex.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hSelf := candidate.datum.sourceEndpoint_self vertex.1
        rw [hPlace] at hSelf
        change (fineCandidate input profile).datum.sourceEndpoint
          (oldVertex target wall) vertex.1.1.2 = vertex.1 at hSelf
        have hLe := fine_left_valency_le_two input profile vertex.1.1.2
        rw [hSelf] at hLe
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (fineCandidate input profile).datum vertex.1 at hGe
        omega
      · obtain ⟨old, hOldTarget, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hPlace
        have hOldAway : old.1.1 ≠ wall := by
          intro hOldWall
          exact hAt (hOldTarget.symm.trans hOldWall)
        have hValency := nonDanglingValency_retainedVertex candidate input.valid
          (fineCandidate_sourceGenus input profile) old hOldAway
        rw [hRetained] at hValency
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          rw [← hValency]
          exact vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        exact (fineBranchVertexMap_of_away input profile oldBranch hOldAway).trans hRetained
  | inr point =>
      cases point
      have hSelf := candidate.datum.sourceEndpoint_self vertex.1
      rw [hPlace] at hSelf
      change (fineCandidate input profile).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 = vertex.1 at hSelf
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hTwo := fine_fresh_selected_valency_le_two input profile vertex.1.1.2 hSelected
        rw [hSelf] at hTwo
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (fineCandidate input profile).datum vertex.1 at hGe
        omega
      · let old := data.sourceEndpoint wall vertex.1.1.2
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          have hValency := fine_nonDanglingValency_background input profile
            vertex.1.1.2 hSelected
          change 3 ≤ nonDanglingValency data (data.sourceEndpoint wall vertex.1.1.2)
          rw [← hValency]
          exact hSelf.symm ▸ vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        have hAt : oldBranch.1.1.1 = wall := rfl
        have hMap := fineBranchVertexMap_of_wall input profile oldBranch hAt
        exact hMap.trans ((fine_fresh_endpoint_wall_repr input profile
          vertex.1.1.2 hSelected).trans hSelf)

/-- The actual branch-vertex equivalence for the fine Figure 31 member. -/
noncomputable def fineBranchVertexEquiv
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BranchVertex data ≃ BranchVertex (fineCandidate input profile).datum :=
  Equiv.ofBijective (fineBranchVertexMap input profile)
    ⟨fineBranchVertexMap_injective input profile,
      fineBranchVertexMap_surjective input profile⟩

@[simp] theorem fineBranchVertexEquiv_apply
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) :
    fineBranchVertexEquiv input profile vertex =
      fineBranchVertexMap input profile vertex := rfl

/-- Lift the literal background replacement to surviving occurrences, using
an actual old incidence as the survival witness. -/
noncomputable def fineBackgroundReplaceEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    NonDanglingEdge (fineCandidate input profile).datum :=
  ⟨fineBackgroundReplace input profile old.1, by
    have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
    have hNewMem := (fineBackgroundReplace_mem_iff input profile sheet hBackground
      old.1).mpr hOldMem
    exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.1⟩

theorem fineBackgroundReplaceEdge_incident
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    Incident (fineCandidate input profile).datum
      (fineBackgroundReplaceEdge input profile sheet hBackground old hIncident).1
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) := by
  have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
  have hNewMem := (fineBackgroundReplace_mem_iff input profile sheet hBackground
    old.1).mpr hOldMem
  exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.2

/-- The checked row equivalence sends an old background occurrence to the
stable row of its literal replacement. -/
theorem fineStablePathEquiv_backgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    fineStablePathEquiv input profile old.stablePath =
      (fineBackgroundReplaceEdge input profile sheet hBackground old hIncident).stablePath := by
  by_cases hTarget : old.1.1.1 = largeTarget input profile
  · have hWall : (data.vertexPartition wall).Rel sheet old.1.1.2 := by
      have hRel := (incident_iff_target_mem_and_rel data old.1 _).mp hIncident |>.2
      change (data.vertexPartition wall).Rel
        ((data.vertexPartition wall).repr sheet) old.1.1.2 at hRel
      exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
    have hOldBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.1.2 := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    have hCanonical : data.sourceEdge (largeTarget input profile) old.1.1.2 = old.1 := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data old.1
    have hCanonicalSurvives : ¬ IsDangling data
        (data.sourceEdge (largeTarget input profile) old.1.1.2) := by
      rw [hCanonical]
      exact old.2
    rw [fineStablePathEquiv_mk]
    calc
      (retainedEdge (fineCandidate input profile) input.valid.1 old).stablePath =
          NonDanglingEdge.stablePath
            ⟨(fineCandidate input profile).oldSourceEdge
                (data.sourceEdge (largeTarget input profile) old.1.1.2),
              not_isDangling_oldSourceEdge _ input.valid.1 _ hCanonicalSurvives⟩ := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg (fineCandidate input profile).oldSourceEdge hCanonical.symm
      _ = NonDanglingEdge.stablePath
            ⟨(fineCandidate input profile).newSourceEdge old.1.1.2,
              (fine_background_new_survives_iff_oldLarge input profile
                old.1.1.2 hOldBackground).mpr hCanonicalSurvives⟩ :=
        (fine_background_new_stablePath_eq_oldLarge input profile old.1.1.2
          hOldBackground hCanonicalSurvives).symm
      _ = (fineBackgroundReplaceEdge input profile sheet hBackground old hIncident).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact (fineBackgroundReplace_of_large input profile old.1 hTarget).symm
  · rw [fineStablePathEquiv_mk]
    apply congrArg NonDanglingEdge.stablePath
    apply Subtype.ext
    exact (fineBackgroundReplace_of_ne_large input profile old.1 hTarget).symm

/-- The background wall branch and its new fresh image have identical
incidence multiplicity in every stable row.  The filtered-star bijection
counts the two flags of a stable loop separately. -/
theorem fine_incidenceCount_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)
        (fineStablePathEquiv input profile path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij
    (fun edge hEdge ↦ fineBackgroundReplaceEdge input profile sheet hBackground edge
      ((mem_incidentEdges data (data.sourceEndpoint wall sheet) edge).mp
        (Finset.mem_filter.mp hEdge).1))
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (fineBackgroundReplaceEdge_incident input profile sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← fineStablePathEquiv_backgroundReplace input profile sheet hBackground edge
      ((mem_incidentEdges _ _ _).mp hIncident), hRow]
  · intro first hFirst second hSecond hEqual
    apply Subtype.ext
    apply fineBackgroundReplace_injective_on_incidence input profile sheet hBackground
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨first.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hFirst).1⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨second.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hSecond).1⟩
    · exact congrArg Subtype.val hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨old, hOldIncident, hReplace, hOldRow⟩ :=
      fineRowOfEdge_incident_background input profile sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)
    have hMapped : fineBackgroundReplaceEdge input profile sheet hBackground old
        hOldIncident = edge := by
      apply Subtype.ext
      exact hReplace
    have hOldPath : old.stablePath = path := by
      apply (fineStablePathEquiv input profile).injective
      rw [fineStablePathEquiv_backgroundReplace input profile sheet hBackground old
        hOldIncident, hMapped, hRow]
    refine ⟨old, ?_, hMapped⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr hOldIncident, hOldPath⟩

/-- The true fine Figure 31 member has the same stable incidence graph as
the original cover.  Both vertex and row maps are the explicit geometric
maps proved above and in `W3Nd2FineRowDescent`. -/
noncomputable def fineStableGraphEquivalence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StableGraphIncidence.Equivalence data (fineCandidate input profile).datum where
  vertex := fineBranchVertexEquiv input profile
  row := fineStablePathEquiv input profile
  incidence vertex path := by
    change incidenceCount data vertex.1 path =
      incidenceCount (fineCandidate input profile).datum
        (fineBranchVertexMap input profile vertex).1
        (fineStablePathEquiv input profile path)
    by_cases hAt : vertex.1.1.1 = wall
    · rw [fineBranchVertexMap_of_wall input profile vertex hAt]
      have hSelf := data.sourceEndpoint_self vertex.1
      rw [hAt] at hSelf
      exact (congrArg (fun sourceVertex ↦ incidenceCount data sourceVertex path)
        hSelf).symm.trans (fine_incidenceCount_background input profile
          vertex.1.1.2 (old_wall_branch_background input profile vertex hAt) path)
    · rw [fineBranchVertexMap_of_away input profile vertex hAt]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex
        (fineCandidate input profile) input.valid
        (fineCandidate_sourceGenus input profile)
        (fineStablePathEquiv input profile)
        (fineStablePathEquiv_mk input profile) vertex.1 hAt path

theorem fineStableGraphEquivalence_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineStableGraphEquivalence input profile).row =
      fineStablePathEquiv input profile := rfl

theorem fineStableGraphEquivalence_vertex_apply
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) :
    (fineStableGraphEquivalence input profile).vertex vertex =
      fineBranchVertexMap input profile vertex := rfl

theorem fine_hasPathEnds
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (hEnds : HasPathEnds data) :
    HasPathEnds (fineCandidate input profile).datum :=
  (fineStableGraphEquivalence input profile).hasPathEnds input.valid.1 hEnds

end DraismaVargas.LocalCases.W3Nd2FineStableGraph
