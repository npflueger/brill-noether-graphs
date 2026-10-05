module

public import DraismaVargas.LocalCases.W3Nd2Survival
public import DraismaVargas.LocalCases.LimitChainCore

@[expose] public section

/-!
# Opposite-end rows for the true Figure 31 candidates

This file classifies the complete surviving incidence at the selected endpoint
not handled by `W3Nd2Survival`.  Old surviving occurrences are transported
back through the contraction and identified with the source profile's literal
small/large pair; the selected new partition contributes one occurrence.
-/

namespace DraismaVargas.LocalCases.W3Nd2EndRows

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival ResolutionM11 ResolutionPruning
open ResolutionSurvival M11SplitRows M11SplitSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! `old_incident_fresh_selected_info`: an old occurrence incident at a
selected fresh endpoint was already incident to the distinguished source
vertex, and the conclusion retains the literal side assignment, which excludes
the wrong member of the profile's two-survivor pair.  Stated for an arbitrary
candidate, it lives in `LimitChainCore` and is re-exported here under its
original name. -/
export LimitChainCore (old_incident_fresh_selected_info)

theorem fine_new_eq_anchor_of_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hIncident : Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile))) :
    (fineCandidate input profile).newSourceEdge sheet =
      (fineCandidate input profile).newSourceEdge (anchor input profile) := by
  let candidate := fineCandidate input profile
  let pasted := finePastedResolution input profile
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target)
      (anchor input profile))).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr (anchor input profile))
      (pasted.newEdge.repr sheet) at hOutgoing
  have hRightRel : pasted.right.Rel (anchor input profile)
      (pasted.newEdge.repr sheet) :=
    (pasted.right.rel_repr_right (anchor input profile)).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈
      pasted.right.block (anchor input profile) :=
    (pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [pasted_right_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile),
    ← pasted_newEdge_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile)] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff
    (anchor input profile) (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr (anchor input profile)
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

theorem coarse_new_eq_anchor_of_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hIncident : Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile))) :
    (coarseCandidate input profile).newSourceEdge sheet =
      (coarseCandidate input profile).newSourceEdge (anchor input profile) := by
  let candidate := coarseCandidate input profile
  let pasted := coarsePastedResolution input profile
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (freshVertex target)
      (anchor input profile))).mp hIncident
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr (anchor input profile))
      (pasted.newEdge.repr sheet) at hOutgoing
  have hRightRel : pasted.right.Rel (anchor input profile)
      (pasted.newEdge.repr sheet) :=
    (pasted.right.rel_repr_right (anchor input profile)).trans hOutgoing.2
  have hMem : pasted.newEdge.repr sheet ∈
      pasted.right.block (anchor input profile) :=
    (pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [coarse_pasted_right_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile),
    ← coarse_pasted_newEdge_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile)] at hMem
  have hNewRel := (pasted.newEdge.mem_block_iff
    (anchor input profile) (pasted.newEdge.repr sheet)).mp hMem
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change pasted.newEdge.repr sheet = pasted.newEdge.repr (anchor input profile)
    exact (pasted.newEdge.repr_idem sheet).symm.trans hNewRel.symm

theorem fine_anchor_new_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (anchor input profile))
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    (fineCandidate input profile).right (finePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (fineCandidate input profile).exterior) (anchor input profile)))

theorem fine_small_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge profile.small.1)
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) := by
  let candidate := fineCandidate input profile
  have hRight : candidate.right (smallTarget input profile) = true := by
    change rightOf (largeTarget input profile) (smallTarget input profile) = true
    simp [rightOf, profile.target_ne]
  simpa only [GluingDatum.sourceEdge_self] using oldSourceEdge_incident_fresh
    candidate _ (smallTarget_mem input profile) hRight (anchor input profile)

theorem fine_nonDanglingIncident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingIncident (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
          (anchor input profile)) =
      {(fineCandidate input profile).newSourceEdge (anchor input profile),
        (fineCandidate input profile).oldSourceEdge profile.small.1} := by
  classical
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (freshVertex target)
    (anchor input profile)
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, hOld⟩ | ⟨sheet, hNew⟩
    · subst edge
      have hInfo := old_incident_fresh_selected_info candidate input.distinguishedBlock
        (anchor input profile) (anchor_wall_rel input profile) old hIncident
      let oldIncident : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) := ⟨old, hInfo.1⟩
      have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((fine_old_isDangling_iff input profile old).mpr hDangling)
      have hProfile := (mem_survivors data input.distinguishedBlock oldIncident).mpr
        hOldSurvives
      rw [profile.surviving] at hProfile
      rcases Finset.mem_insert.mp hProfile with hSmall | hLarge
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            candidate.oldSourceEdge item.1) hSmall
      · have hOldLarge := congrArg
          (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ item.1)
          (Finset.mem_singleton.mp hLarge)
        change old = profile.large.1 at hOldLarge
        have hTargetLarge := congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hOldLarge
        have hWrong : candidate.right (largeTarget input profile) = true := by
          exact (congrArg candidate.right hTargetLarge.symm).trans hInfo.2
        change rightOf (largeTarget input profile) (largeTarget input profile) = true at hWrong
        simp [rightOf] at hWrong
    · subst edge
      apply Finset.mem_insert.mpr
      exact Or.inl (fine_new_eq_anchor_of_incident_right input profile sheet hIncident)
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hNew | hSmall
    · rw [hNew]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨fine_anchor_new_survives input profile,
          fine_anchor_new_incident_right input profile⟩
    · rw [Finset.mem_singleton] at hSmall
      rw [hSmall]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨fine_small_survives input profile, fine_small_incident_right input profile⟩

theorem fine_right_nonDanglingValency_eq_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingValency (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) = 2 := by
  rw [← card_nonDanglingIncident, fine_nonDanglingIncident_right input profile]
  apply Finset.card_pair
  intro hEqual
  have hTargets := congrArg
    (fun edge : (fineCandidate input profile).datum.SourceEdge ↦ edge.1.1) hEqual
  have hLabels := (occurrenceEquiv target wall
    (fineCandidate input profile).right).injective hTargets
  cases hLabels

noncomputable def fineRetainedSmall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (fineCandidate input profile).datum :=
  ⟨(fineCandidate input profile).oldSourceEdge profile.small.1,
    fine_small_survives input profile⟩

theorem fine_anchor_new_consecutive_small (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Consecutive (fineCandidate input profile).datum
      (fineAnchorNew input profile) (fineRetainedSmall input profile) := by
  refine ⟨?_, _, fine_anchor_new_incident_right input profile,
    fine_small_incident_right input profile,
    fine_right_nonDanglingValency_eq_two input profile⟩
  intro hEqual
  have hTargets := congrArg
    (fun edge : NonDanglingEdge (fineCandidate input profile).datum ↦ edge.1.1.1)
    hEqual
  have hLabels := (occurrenceEquiv target wall
    (fineCandidate input profile).right).injective hTargets
  cases hLabels

/-- At its trivalent-side endpoint, the same surviving fine new occurrence
inherits the stable row of the old small survivor. -/
theorem fine_anchor_new_stablePath_eq_small (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineAnchorNew input profile).stablePath =
      (fineRetainedSmall input profile).stablePath :=
  stablePath_eq_of_consecutive (fine_anchor_new_consecutive_small input profile)

theorem coarse_anchor_new_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge (anchor input profile))
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile).right (coarsePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile).exterior) (anchor input profile)))

theorem coarse_large_incident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge profile.large.1)
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) := by
  let candidate := coarseCandidate input profile
  have hRight : candidate.right (largeTarget input profile) = true := by
    change rightOf (smallTarget input profile) (largeTarget input profile) = true
    simp [rightOf, profile.target_ne.symm]
  have hIncident := oldSourceEdge_incident_fresh candidate _
    (largeTarget_mem input profile) hRight profile.large.1.1.2
  have hWallLarge : (data.vertexPartition wall).Rel (anchor input profile)
      profile.large.1.1.2 := by
    have hMem : profile.large.1.1.2 ∈
        (data.vertexPartition wall).block input.distinguishedBlock.1 := by
      rw [← large_block_eq_wall input profile]
      exact (data.edgePartition (largeTarget input profile)).self_mem_block _
    exact (anchor_wall_rel input profile).symm.trans
      (((data.vertexPartition wall).mem_block_iff _ _).mp hMem)
  have hVertex : candidate.datum.sourceEndpoint (freshVertex target)
      (anchor input profile) = candidate.datum.sourceEndpoint (freshVertex target)
        profile.large.1.1.2 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile).right.repr (anchor input profile) =
        (coarsePastedResolution input profile).right.repr profile.large.1.1.2
      have hMem : profile.large.1.1.2 ∈
          (coarsePastedResolution input profile).right.block
            (anchor input profile) := by
        rw [coarse_pasted_right_block_selected input profile (anchor input profile)
          (anchor_wall_rel input profile)]
        exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hWallLarge
      exact ((coarsePastedResolution input profile).right.mem_block_iff _ _).mp hMem
  rw [hVertex]
  simpa only [GluingDatum.sourceEdge_self] using hIncident

theorem coarse_nonDanglingIncident_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingIncident (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
          (anchor input profile)) =
      {(coarseCandidate input profile).newSourceEdge (anchor input profile),
        (coarseCandidate input profile).oldSourceEdge profile.large.1} := by
  classical
  let candidate := coarseCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (freshVertex target)
    (anchor input profile)
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, hOld⟩ | ⟨sheet, hNew⟩
    · subst edge
      have hInfo := old_incident_fresh_selected_info candidate input.distinguishedBlock
        (anchor input profile) (anchor_wall_rel input profile) old hIncident
      let oldIncident : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) := ⟨old, hInfo.1⟩
      have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((coarse_old_isDangling_iff input profile old).mpr hDangling)
      have hProfile := (mem_survivors data input.distinguishedBlock oldIncident).mpr
        hOldSurvives
      rw [profile.surviving] at hProfile
      rcases Finset.mem_insert.mp hProfile with hSmall | hLarge
      · have hOldSmall := congrArg
          (fun item : IncidentSourceEdge data
            (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ item.1) hSmall
        change old = profile.small.1 at hOldSmall
        have hTargetSmall := congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hOldSmall
        have hWrong : candidate.right (smallTarget input profile) = true := by
          exact (congrArg candidate.right hTargetSmall.symm).trans hInfo.2
        change rightOf (smallTarget input profile) (smallTarget input profile) = true at hWrong
        simp [rightOf] at hWrong
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact congrArg (fun item : IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
            candidate.oldSourceEdge item.1) (Finset.mem_singleton.mp hLarge)
    · subst edge
      apply Finset.mem_insert.mpr
      exact Or.inl (coarse_new_eq_anchor_of_incident_right input profile sheet hIncident)
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hNew | hLarge
    · rw [hNew]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨coarse_anchor_new_survives input profile,
          coarse_anchor_new_incident_right input profile⟩
    · rw [Finset.mem_singleton] at hLarge
      rw [hLarge]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨coarse_large_survives input profile, coarse_large_incident_right input profile⟩

theorem coarse_right_nonDanglingValency_eq_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    nonDanglingValency (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (anchor input profile)) = 2 := by
  rw [← card_nonDanglingIncident, coarse_nonDanglingIncident_right input profile]
  apply Finset.card_pair
  intro hEqual
  have hTargets := congrArg
    (fun edge : (coarseCandidate input profile).datum.SourceEdge ↦ edge.1.1) hEqual
  have hLabels := (occurrenceEquiv target wall
    (coarseCandidate input profile).right).injective hTargets
  cases hLabels

noncomputable def coarseRetainedLarge (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (coarseCandidate input profile).datum :=
  ⟨(coarseCandidate input profile).oldSourceEdge profile.large.1,
    coarse_large_survives input profile⟩

theorem coarse_anchor_new_consecutive_large (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Consecutive (coarseCandidate input profile).datum
      (coarseAnchorNew input profile) (coarseRetainedLarge input profile) := by
  refine ⟨?_, _, coarse_anchor_new_incident_right input profile,
    coarse_large_incident_right input profile,
    coarse_right_nonDanglingValency_eq_two input profile⟩
  intro hEqual
  have hTargets := congrArg
    (fun edge : NonDanglingEdge (coarseCandidate input profile).datum ↦ edge.1.1.1)
    hEqual
  have hLabels := (occurrenceEquiv target wall
    (coarseCandidate input profile).right).injective hTargets
  cases hLabels

/-- At its right endpoint, the unique coarse selected new occurrence inherits
the stable row of the old large survivor. -/
theorem coarse_anchor_new_stablePath_eq_large (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (coarseAnchorNew input profile).stablePath =
      (coarseRetainedLarge input profile).stablePath :=
  stablePath_eq_of_consecutive (coarse_anchor_new_consecutive_large input profile)

end DraismaVargas.LocalCases.W3Nd2EndRows
