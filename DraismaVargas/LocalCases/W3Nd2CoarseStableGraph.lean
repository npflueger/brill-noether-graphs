module

public import DraismaVargas.LocalCases.W3Nd2RowDescent
public import DraismaVargas.LocalCases.ResolutionStableIncidence
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# Stable-incidence certificate for the true Figure 31 coarse member

Figure 31 is Case {w3-r1-nd2} of Draisma--Vargas Part I.
Old branches away from the resolved wall are retained.  Since the selected
old wall block is divalent, every old wall branch is a background block and
maps to the corresponding fresh endpoint.  The expanded left endpoints and
the selected fresh endpoint have surviving valency at most two, so these are
all candidate branches.
-/

namespace DraismaVargas.LocalCases.W3Nd2CoarseStableGraph

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2EndRows W3Nd2Background
open W3Nd2StableLift W3Nd2RowDescent ResolutionM11 ResolutionPruning
open ResolutionSurvival ResolutionAwayFromWall ResolutionStableIncidence
open StableGraphIncidence StablePathCount NonDanglingValency

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-- The selected coarse left endpoint has exactly the anchor-new and retained
small survivors; the residual small occurrence supplies the deleted third
flag. -/
theorem coarse_selected_left_valency_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingValency (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) = 2 := by
  classical
  let candidate := coarseCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) (anchor input profile)
  change nonDanglingValency candidate.datum vertex = 2
  let dangling : IncidentSourceEdge candidate.datum vertex :=
    ⟨candidate.oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile)),
      coarse_residual_oldSmall_incident_left input profile⟩
  have hDanglingPositive : 0 <
      ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
        (fun edge ↦ IsDangling candidate.datum edge.1)).card :=
    Finset.card_pos.mpr ⟨dangling, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, coarse_residual_oldSmall_dangles input profile⟩⟩
  have hSurvivingPositive :=
    ClassInjectivity.nonDanglingValency_ne_zero_of_incident candidate.datum
      (coarse_anchor_new_survives input profile)
      (coarse_anchor_new_incident_left input profile)
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one candidate.datum
    (coarseCandidate_valid input profile).1 vertex
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    coarse_left_card_three input profile] at hTotal
  dsimp only [candidate, vertex] at hDanglingPositive hSurvivingPositive hNotOne hTotal ⊢
  omega

/-- Every expanded old-wall endpoint of the coarse candidate has surviving
valency at most two. -/
theorem coarse_left_valency_le_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree) :
    nonDanglingValency (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2 := by
  by_cases hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet
  · have hEndpoint := coarse_left_endpoint_eq_of_wall_rel input profile
      (anchor input profile) sheet (anchor_wall_rel input profile)
      ((anchor_wall_rel input profile).symm.trans hSelected)
    rw [← hEndpoint, coarse_selected_left_valency_two input profile]
  · have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
      (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) sheet)
    rw [coarse_background_left_card_two input profile sheet hSelected] at hUpper
    exact hUpper

theorem coarse_fresh_endpoint_eq_anchor_of_selected
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet =
      (coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile).right.repr sheet =
      (coarsePastedResolution input profile).right.repr (anchor input profile)
    apply (coarsePastedResolution input profile).right.mem_block_iff _ _ |>.mp
    rw [coarse_pasted_right_block_selected input profile sheet hSelected]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      (hSelected.symm.trans (anchor_wall_rel input profile))

theorem coarse_fresh_selected_valency_two
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    nonDanglingValency (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
  rw [coarse_fresh_endpoint_eq_anchor_of_selected input profile sheet hSelected,
    coarse_right_nonDanglingValency_eq_two input profile]

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
noncomputable def coarseBackgroundFreshBranch
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data)
    (hAt : vertex.1.1.1 = wall) :
    BranchVertex (coarseCandidate input profile).datum :=
  ⟨(coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
      vertex.1.1.2, by
    rw [coarse_nonDanglingValency_background input profile vertex.1.1.2
      (old_wall_branch_background input profile vertex hAt)]
    have hSelf := data.sourceEndpoint_self vertex.1
    rw [hAt] at hSelf
    rw [hSelf]
    exact vertex.2⟩

/-- An old branch away from the wall is retained literally. -/
noncomputable def coarseRetainedBranch
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data)
    (hAway : vertex.1.1.1 ≠ wall) :
    BranchVertex (coarseCandidate input profile).datum :=
  ⟨retainedVertex (coarseCandidate input profile) vertex.1, by
    rw [nonDanglingValency_retainedVertex _ input.valid
      (coarseCandidate_sourceGenus input profile) vertex.1 hAway]
    exact vertex.2⟩

/-- The actual coarse branch map: wall-background branches move to the fresh
side and all off-wall branches are retained. -/
noncomputable def coarseBranchVertexMap
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BranchVertex data → BranchVertex (coarseCandidate input profile).datum :=
  fun vertex ↦ if hAt : vertex.1.1.1 = wall then
    coarseBackgroundFreshBranch input profile vertex hAt
  else coarseRetainedBranch input profile vertex hAt

theorem coarseBranchVertexMap_of_wall
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) (hAt : vertex.1.1.1 = wall) :
    (coarseBranchVertexMap input profile vertex).1 =
      (coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        vertex.1.1.2 := by
  unfold coarseBranchVertexMap
  exact congrArg Subtype.val (dite_eq_left hAt)

theorem coarseBranchVertexMap_of_away
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) (hAway : vertex.1.1.1 ≠ wall) :
    (coarseBranchVertexMap input profile vertex).1 =
      retainedVertex (coarseCandidate input profile) vertex.1 := by
  unfold coarseBranchVertexMap
  exact congrArg Subtype.val (dite_eq_right hAway)

/-- On background blocks, equality of fresh endpoints reflects equality of
the corresponding old wall endpoints. -/
theorem coarse_fresh_endpoint_reflects_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : Fin degree)
    (hFirst : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hEqual : (coarseCandidate input profile).datum.sourceEndpoint
        (freshVertex target) first =
      (coarseCandidate input profile).datum.sourceEndpoint
        (freshVertex target) second) :
    data.sourceEndpoint wall first = data.sourceEndpoint wall second := by
  have hRight : (coarsePastedResolution input profile).right.Rel first second := by
    change (coarsePastedResolution input profile).right.repr first =
      (coarsePastedResolution input profile).right.repr second
    exact congrArg (fun vertex : (coarseCandidate input profile).datum.SourceVertex ↦
      vertex.1.2) hEqual
  have hWall : (data.vertexPartition wall).Rel first second := by
    apply (data.vertexPartition wall).mem_block_iff _ _ |>.mp
    rw [← coarse_background_right_block input profile first hFirst,
      (coarsePastedResolution input profile).right.mem_block_iff]
    exact hRight
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hWall

/-- Replacing a background sheet by its old wall representative does not
change the corresponding coarse fresh endpoint. -/
theorem coarse_fresh_endpoint_wall_repr
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        ((data.vertexPartition wall).repr sheet) =
      (coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile).right.repr
      ((data.vertexPartition wall).repr sheet) =
        (coarsePastedResolution input profile).right.repr sheet
    symm
    apply (coarsePastedResolution input profile).right.mem_block_iff _ _ |>.mp
    rw [coarse_background_right_block input profile sheet hBackground]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((data.vertexPartition wall).rel_repr_right sheet)

theorem coarseBranchVertexMap_injective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Injective (coarseBranchVertexMap input profile) := by
  intro first second hEqual
  let candidate := coarseCandidate input profile
  by_cases hFirst : first.1.1.1 = wall
  · by_cases hSecond : second.1.1.1 = wall
    · apply Subtype.ext
      have hFirstMap := coarseBranchVertexMap_of_wall input profile first hFirst
      have hSecondMap := coarseBranchVertexMap_of_wall input profile second hSecond
      have hFresh := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hOld := coarse_fresh_endpoint_reflects_background input profile
        first.1.1.2 second.1.1.2
        (old_wall_branch_background input profile first hFirst) hFresh
      have hFirstSelf := data.sourceEndpoint_self first.1
      have hSecondSelf := data.sourceEndpoint_self second.1
      rw [hFirst] at hFirstSelf
      rw [hSecond] at hSecondSelf
      exact hFirstSelf.symm.trans (hOld.trans hSecondSelf)
    · have hFirstMap := coarseBranchVertexMap_of_wall input profile first hFirst
      have hSecondMap := coarseBranchVertexMap_of_away input profile second hSecond
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
  · by_cases hSecond : second.1.1.1 = wall
    · have hFirstMap := coarseBranchVertexMap_of_away input profile first hFirst
      have hSecondMap := coarseBranchVertexMap_of_wall input profile second hSecond
      have hValues := hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)
      have hTargets := congrArg
        (fun vertex : candidate.datum.SourceVertex ↦ vertex.1.1) hValues
      cases hTargets
    · apply Subtype.ext
      apply retainedVertex_injective_away candidate first.1 second.1 hFirst hSecond
      have hFirstMap := coarseBranchVertexMap_of_away input profile first hFirst
      have hSecondMap := coarseBranchVertexMap_of_away input profile second hSecond
      exact hFirstMap.symm.trans ((congrArg Subtype.val hEqual).trans hSecondMap)

theorem coarseBranchVertexMap_surjective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Surjective (coarseBranchVertexMap input profile) := by
  intro vertex
  let candidate := coarseCandidate input profile
  cases hPlace : vertex.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hSelf := candidate.datum.sourceEndpoint_self vertex.1
        rw [hPlace] at hSelf
        change (coarseCandidate input profile).datum.sourceEndpoint
          (oldVertex target wall) vertex.1.1.2 = vertex.1 at hSelf
        have hLe := coarse_left_valency_le_two input profile vertex.1.1.2
        rw [hSelf] at hLe
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (coarseCandidate input profile).datum vertex.1 at hGe
        omega
      · obtain ⟨old, hOldTarget, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hPlace
        have hOldAway : old.1.1 ≠ wall := by
          intro hOldWall
          exact hAt (hOldTarget.symm.trans hOldWall)
        have hValency := nonDanglingValency_retainedVertex candidate input.valid
          (coarseCandidate_sourceGenus input profile) old hOldAway
        rw [hRetained] at hValency
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          rw [← hValency]
          exact vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        exact (coarseBranchVertexMap_of_away input profile oldBranch hOldAway).trans hRetained
  | inr point =>
      cases point
      have hSelf := candidate.datum.sourceEndpoint_self vertex.1
      rw [hPlace] at hSelf
      change (coarseCandidate input profile).datum.sourceEndpoint
        (freshVertex target) vertex.1.1.2 = vertex.1 at hSelf
      by_cases hSelected : (data.vertexPartition wall).Rel
          input.distinguishedBlock.1 vertex.1.1.2
      · have hTwo := coarse_fresh_selected_valency_two input profile vertex.1.1.2 hSelected
        rw [hSelf] at hTwo
        have hGe := vertex.2
        change 3 ≤ nonDanglingValency (coarseCandidate input profile).datum vertex.1 at hGe
        omega
      · let old := data.sourceEndpoint wall vertex.1.1.2
        have hOldBranch : 3 ≤ nonDanglingValency data old := by
          have hValency := coarse_nonDanglingValency_background input profile
            vertex.1.1.2 hSelected
          change 3 ≤ nonDanglingValency data (data.sourceEndpoint wall vertex.1.1.2)
          rw [← hValency]
          exact hSelf.symm ▸ vertex.2
        let oldBranch : BranchVertex data := ⟨old, hOldBranch⟩
        refine ⟨oldBranch, ?_⟩
        apply Subtype.ext
        have hAt : oldBranch.1.1.1 = wall := rfl
        have hMap := coarseBranchVertexMap_of_wall input profile oldBranch hAt
        exact hMap.trans ((coarse_fresh_endpoint_wall_repr input profile
          vertex.1.1.2 hSelected).trans hSelf)

/-- The actual branch-vertex equivalence for the coarse Figure 31 member. -/
noncomputable def coarseBranchVertexEquiv
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BranchVertex data ≃ BranchVertex (coarseCandidate input profile).datum :=
  Equiv.ofBijective (coarseBranchVertexMap input profile)
    ⟨coarseBranchVertexMap_injective input profile,
      coarseBranchVertexMap_surjective input profile⟩

@[simp] theorem coarseBranchVertexEquiv_apply
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) :
    coarseBranchVertexEquiv input profile vertex =
      coarseBranchVertexMap input profile vertex := rfl

/-- Lift the literal background replacement to surviving occurrences, using
an actual old incidence as the survival witness. -/
noncomputable def coarseBackgroundReplaceEdge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    NonDanglingEdge (coarseCandidate input profile).datum :=
  ⟨coarseBackgroundReplace input profile old.1, by
    have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
    have hNewMem := (coarseBackgroundReplace_mem_iff input profile sheet hBackground
      old.1).mpr hOldMem
    exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.1⟩

theorem coarseBackgroundReplaceEdge_incident
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    Incident (coarseCandidate input profile).datum
      (coarseBackgroundReplaceEdge input profile sheet hBackground old hIncident).1
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) := by
  have hOldMem : old.1 ∈ nonDanglingIncident data (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨old.2, hIncident⟩
  have hNewMem := (coarseBackgroundReplace_mem_iff input profile sheet hBackground
    old.1).mpr hOldMem
  exact (mem_nonDanglingIncident _ _ _).mp hNewMem |>.2

/-- The checked row equivalence sends an old background occurrence to the
stable row of its literal replacement. -/
theorem coarseStablePathEquiv_backgroundReplace
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : NonDanglingEdge data)
    (hIncident : Incident data old.1 (data.sourceEndpoint wall sheet)) :
    coarseStablePathEquiv input profile old.stablePath =
      (coarseBackgroundReplaceEdge input profile sheet hBackground old hIncident).stablePath := by
  by_cases hTarget : old.1.1.1 = smallTarget input profile
  · have hWall : (data.vertexPartition wall).Rel sheet old.1.1.2 := by
      have hRel := (incident_iff_target_mem_and_rel data old.1 _).mp hIncident |>.2
      change (data.vertexPartition wall).Rel
        ((data.vertexPartition wall).repr sheet) old.1.1.2 at hRel
      exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
    have hOldBackground : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 old.1.1.2 := by
      intro hSelected
      exact hBackground (hSelected.trans hWall.symm)
    have hCanonical : data.sourceEdge (smallTarget input profile) old.1.1.2 = old.1 := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data old.1
    have hCanonicalSurvives : ¬ IsDangling data
        (data.sourceEdge (smallTarget input profile) old.1.1.2) := by
      rw [hCanonical]
      exact old.2
    rw [coarseStablePathEquiv_mk]
    calc
      (retainedEdge (coarseCandidate input profile) input.valid.1 old).stablePath =
          NonDanglingEdge.stablePath
            ⟨(coarseCandidate input profile).oldSourceEdge
                (data.sourceEdge (smallTarget input profile) old.1.1.2),
              not_isDangling_oldSourceEdge _ input.valid.1 _ hCanonicalSurvives⟩ := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg (coarseCandidate input profile).oldSourceEdge hCanonical.symm
      _ = NonDanglingEdge.stablePath
            ⟨(coarseCandidate input profile).newSourceEdge old.1.1.2,
              (coarse_background_new_survives_iff_oldSmall input profile
                old.1.1.2 hOldBackground).mpr hCanonicalSurvives⟩ :=
        (coarse_background_new_stablePath_eq_oldSmall input profile old.1.1.2
          hOldBackground hCanonicalSurvives).symm
      _ = (coarseBackgroundReplaceEdge input profile sheet hBackground old hIncident).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact (coarseBackgroundReplace_of_small input profile old.1 hTarget).symm
  · rw [coarseStablePathEquiv_mk]
    apply congrArg NonDanglingEdge.stablePath
    apply Subtype.ext
    exact (coarseBackgroundReplace_of_ne_small input profile old.1 hTarget).symm

/-- The background wall branch and its new fresh image have identical
incidence multiplicity in every stable row.  The filtered-star bijection
counts the two flags of a stable loop separately. -/
theorem coarse_incidenceCount_background
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)
        (coarseStablePathEquiv input profile path) := by
  classical
  unfold incidenceCount
  apply Finset.card_bij
    (fun edge hEdge ↦ coarseBackgroundReplaceEdge input profile sheet hBackground edge
      ((mem_incidentEdges data (data.sourceEndpoint wall sheet) edge).mp
        (Finset.mem_filter.mp hEdge).1))
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges _ _ _).mpr
      (coarseBackgroundReplaceEdge_incident input profile sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)), ?_⟩
    rw [← coarseStablePathEquiv_backgroundReplace input profile sheet hBackground edge
      ((mem_incidentEdges _ _ _).mp hIncident), hRow]
  · intro first hFirst second hSecond hEqual
    apply Subtype.ext
    apply coarseBackgroundReplace_injective_on_incidence input profile sheet hBackground
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨first.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hFirst).1⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨second.2, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hSecond).1⟩
    · exact congrArg Subtype.val hEqual
  · intro edge hEdge
    obtain ⟨hIncident, hRow⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨old, hOldIncident, hReplace, hOldRow⟩ :=
      coarseRowOfEdge_incident_background input profile sheet hBackground edge
        ((mem_incidentEdges _ _ _).mp hIncident)
    have hMapped : coarseBackgroundReplaceEdge input profile sheet hBackground old
        hOldIncident = edge := by
      apply Subtype.ext
      exact hReplace
    have hOldPath : old.stablePath = path := by
      apply (coarseStablePathEquiv input profile).injective
      rw [coarseStablePathEquiv_backgroundReplace input profile sheet hBackground old
        hOldIncident, hMapped, hRow]
    refine ⟨old, ?_, hMapped⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr hOldIncident, hOldPath⟩

/-- The true coarse Figure 31 member has the same stable incidence graph as
the original cover.  Both vertex and row maps are the explicit geometric
maps proved above and in `W3Nd2RowDescent`. -/
noncomputable def coarseStableGraphEquivalence
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StableGraphIncidence.Equivalence data (coarseCandidate input profile).datum where
  vertex := coarseBranchVertexEquiv input profile
  row := coarseStablePathEquiv input profile
  incidence vertex path := by
    change incidenceCount data vertex.1 path =
      incidenceCount (coarseCandidate input profile).datum
        (coarseBranchVertexMap input profile vertex).1
        (coarseStablePathEquiv input profile path)
    by_cases hAt : vertex.1.1.1 = wall
    · rw [coarseBranchVertexMap_of_wall input profile vertex hAt]
      have hSelf := data.sourceEndpoint_self vertex.1
      rw [hAt] at hSelf
      exact (congrArg (fun sourceVertex ↦ incidenceCount data sourceVertex path)
        hSelf).symm.trans (coarse_incidenceCount_background input profile
          vertex.1.1.2 (old_wall_branch_background input profile vertex hAt) path)
    · rw [coarseBranchVertexMap_of_away input profile vertex hAt]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex
        (coarseCandidate input profile) input.valid
        (coarseCandidate_sourceGenus input profile)
        (coarseStablePathEquiv input profile)
        (coarseStablePathEquiv_mk input profile) vertex.1 hAt path

theorem coarseStableGraphEquivalence_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (coarseStableGraphEquivalence input profile).row =
      coarseStablePathEquiv input profile := rfl

theorem coarseStableGraphEquivalence_vertex_apply
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (vertex : BranchVertex data) :
    (coarseStableGraphEquivalence input profile).vertex vertex =
      coarseBranchVertexMap input profile vertex := rfl

theorem coarse_hasPathEnds
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (hEnds : HasPathEnds data) :
    HasPathEnds (coarseCandidate input profile).datum :=
  (coarseStableGraphEquivalence input profile).hasPathEnds input.valid.1 hEnds

end DraismaVargas.LocalCases.W3Nd2CoarseStableGraph
