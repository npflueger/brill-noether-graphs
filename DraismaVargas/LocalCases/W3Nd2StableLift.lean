import DraismaVargas.LocalCases.W3Nd2Background
import DraismaVargas.LocalCases.W3Nd2EndRows
import DraismaVargas.LocalCases.ResolutionAwayFromWall
import DraismaVargas.LocalCases.DivalentSourceLocal

/-!
# Stable-row lifts for the true Figure 31 candidates

The map on stable rows retains an old surviving occurrence.  At the
distinguished wall block, both retained survivors meet the selected new arm.
At an unramified background block, the same conclusion follows from the
literal source incidence census; away from the wall, resolution does not
alter consecutive pairs.
-/

namespace DraismaVargas.LocalCases.W3Nd2StableLift

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2EndRows W3Nd2Background
open ResolutionM11 ResolutionPruning ResolutionSurvival ResolutionAwayFromWall
open DivalentSourceLocal

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-- A surviving occurrence at the distinguished source vertex is literally
one of the profile's small/large pair. -/
theorem selected_survivor_eq_small_or_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    edge.1 = profile.small.1 ∨ edge.1 = profile.large.1 := by
  let incident : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
    ⟨edge.1, hIncident⟩
  have hMem := (mem_survivors data input.distinguishedBlock incident).mpr edge.2
  rw [profile.surviving] at hMem
  rcases Finset.mem_insert.mp hMem with hSmall | hLarge
  · exact Or.inl (congrArg Subtype.val hSmall)
  · exact Or.inr (congrArg Subtype.val (Finset.mem_singleton.mp hLarge))

/-- In the coarse member every retained selected survivor has the stable row
of the selected new occurrence. -/
theorem coarse_retained_selected_eq_anchor
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    (retainedEdge (coarseCandidate input profile) input.valid.1 edge).stablePath =
      (coarseAnchorNew input profile).stablePath := by
  rcases selected_survivor_eq_small_or_large input profile edge hIncident with
      hSmall | hLarge
  · have hEdge : retainedEdge (coarseCandidate input profile) input.valid.1 edge =
        coarseRetainedSmall input profile := by
      apply Subtype.ext
      exact congrArg (coarseCandidate input profile).oldSourceEdge hSmall
    rw [hEdge]
    exact (coarse_anchor_new_stablePath_eq_small input profile).symm
  · have hEdge : retainedEdge (coarseCandidate input profile) input.valid.1 edge =
        coarseRetainedLarge input profile := by
      apply Subtype.ext
      exact congrArg (coarseCandidate input profile).oldSourceEdge hLarge
    rw [hEdge]
    exact (coarse_anchor_new_stablePath_eq_large input profile).symm

/-- In the fine member every retained selected survivor has the stable row of
the selected new occurrence. -/
theorem fine_retained_selected_eq_anchor
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data)
    (hIncident : Incident data edge.1
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    (retainedEdge (fineCandidate input profile) input.valid.1 edge).stablePath =
      (fineAnchorNew input profile).stablePath := by
  rcases selected_survivor_eq_small_or_large input profile edge hIncident with
      hSmall | hLarge
  · have hEdge : retainedEdge (fineCandidate input profile) input.valid.1 edge =
        fineRetainedSmall input profile := by
      apply Subtype.ext
      exact congrArg (fineCandidate input profile).oldSourceEdge hSmall
    rw [hEdge]
    exact (fine_anchor_new_stablePath_eq_small input profile).symm
  · have hEdge : retainedEdge (fineCandidate input profile) input.valid.1 edge =
        fineRetainedLarge input profile := by
      apply Subtype.ext
      exact congrArg (fineCandidate input profile).oldSourceEdge hLarge
    rw [hEdge]
    exact (fine_anchor_new_stablePath_eq_large input profile).symm

/-- Both actual background resolutions leave the complete wall block at the
fresh (trivalent) endpoint. -/
theorem coarse_background_right_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_right_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

/-- On a background block an old coarse occurrence is incident at the fresh
endpoint precisely when it was incident at the old wall vertex and does not
point in the selected small direction. -/
theorem coarse_background_old_incident_right_iff
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    Incident (coarseCandidate input profile).datum
        ((coarseCandidate input profile).oldSourceEdge old)
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ smallTarget input profile := by
  let candidate := coarseCandidate input profile
  let targetEdge : target.edges := old.val.fst
  have hTarget : occurrenceEquiv target wall candidate.right (some targetEdge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) ↔
      targetEdge ∈ GluingDatum.incidentEdges wall ∧
        targetEdge ≠ smallTarget input profile := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [occurrenceEquiv_some]
    refine (oldEnds_incident_freshVertex_iff target wall candidate.right targetEdge).trans ?_
    change (_ ∧ rightOf (smallTarget input profile) targetEdge = true) ↔ _
    simp [rightOf]
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ (coarsePastedResolution input profile).right.Rel
      ((coarsePastedResolution input profile).right.repr sheet) old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) old.1.2) ∧ _
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ (coarsePastedResolution input profile).right.Rel sheet old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel sheet old.1.2) ∧ _
  have hRel : (coarsePastedResolution input profile).right.Rel sheet old.1.2 ↔
      (data.vertexPartition wall).Rel sheet old.1.2 := by
    rw [← (coarsePastedResolution input profile).right.mem_block_iff,
      ← (data.vertexPartition wall).mem_block_iff,
      coarse_background_right_block input profile sheet hSheet]
  rw [hRel]
  tauto

theorem fine_background_old_incident_right_iff
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (old : data.SourceEdge) :
    Incident (fineCandidate input profile).datum
        ((fineCandidate input profile).oldSourceEdge old)
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ largeTarget input profile := by
  let candidate := fineCandidate input profile
  let targetEdge : target.edges := old.val.fst
  have hTarget : occurrenceEquiv target wall candidate.right (some targetEdge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) ↔
      targetEdge ∈ GluingDatum.incidentEdges wall ∧
        targetEdge ≠ largeTarget input profile := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [occurrenceEquiv_some]
    refine (oldEnds_incident_freshVertex_iff target wall candidate.right targetEdge).trans ?_
    change (_ ∧ rightOf (largeTarget input profile) targetEdge = true) ↔ _
    simp [rightOf]
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ (finePastedResolution input profile).right.Rel
      ((finePastedResolution input profile).right.repr sheet) old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) old.1.2) ∧ _
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ (finePastedResolution input profile).right.Rel sheet old.1.2) ↔
    (_ ∧ (data.vertexPartition wall).Rel sheet old.1.2) ∧ _
  have hRel : (finePastedResolution input profile).right.Rel sheet old.1.2 ↔
      (data.vertexPartition wall).Rel sheet old.1.2 := by
    rw [← (finePastedResolution input profile).right.mem_block_iff,
      ← (data.vertexPartition wall).mem_block_iff,
      fine_background_right_block input profile sheet hSheet]
  rw [hRel]
  tauto

theorem coarse_background_new_incident_right
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge other)
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) := by
  let candidate := coarseCandidate input profile
  have hOther : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 other := by
    intro hDist
    exact hSheet (hDist.trans hRel.symm)
  have hBase : Incident candidate.datum (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (freshVertex target) other) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      candidate.right (coarsePastedResolution input profile)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) other))
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) other := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (coarsePastedResolution input profile).right.repr sheet =
          (coarsePastedResolution input profile).right.repr other
      apply (coarsePastedResolution input profile).right.mem_block_iff _ _ |>.mp
      rw [coarse_background_right_block input profile sheet hSheet]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hRel
  exact hEndpoint.symm ▸ hBase

theorem fine_background_new_incident_right
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge other)
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) := by
  let candidate := fineCandidate input profile
  have hOther : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 other := by
    intro hDist
    exact hSheet (hDist.trans hRel.symm)
  have hBase : Incident candidate.datum (candidate.newSourceEdge other)
      (candidate.datum.sourceEndpoint (freshVertex target) other) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      candidate.right (finePastedResolution input profile)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) other))
  have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) sheet =
      candidate.datum.sourceEndpoint (freshVertex target) other := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (finePastedResolution input profile).right.repr sheet =
          (finePastedResolution input profile).right.repr other
      apply (finePastedResolution input profile).right.mem_block_iff _ _ |>.mp
      rw [fine_background_right_block input profile sheet hSheet]
      exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr hRel
  exact hEndpoint.symm ▸ hBase

theorem coarse_background_new_incident_right_rel
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hIncident : Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge other)
      ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet other := by
  have hData := (incident_iff_target_mem_and_rel
    (coarseCandidate input profile).datum _ _).mp hIncident |>.2
  change (coarsePastedResolution input profile).right.Rel
      ((coarsePastedResolution input profile).right.repr sheet)
      ((coarsePastedResolution input profile).newEdge.repr other) at hData
  have hRight : (coarsePastedResolution input profile).right.Rel sheet
      ((coarsePastedResolution input profile).newEdge.repr other) :=
    (coarsePastedResolution input profile).right.rel_repr_right sheet |>.trans hData
  have hWallRepr : (data.vertexPartition wall).Rel sheet
      ((coarsePastedResolution input profile).newEdge.repr other) := by
    rw [← (data.vertexPartition wall).mem_block_iff,
      ← coarse_background_right_block input profile sheet hSheet,
      (coarsePastedResolution input profile).right.mem_block_iff]
    exact hRight
  have hRefines : (coarsePastedResolution input profile).newEdge.Refines
      (data.vertexPartition wall) :=
    (coarsePastedResolution input profile).edge_refines_right.trans
      (LocalResolution.pasteRight_refines (data.vertexPartition wall)
        (coarseCandidate input profile).resolution
        (coarseCandidate input profile).contracts)
  exact hWallRepr.trans (hRefines.rel
    ((coarsePastedResolution input profile).newEdge.rel_repr_left other))

theorem fine_background_new_incident_right_rel
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hIncident : Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge other)
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet other := by
  have hData := (incident_iff_target_mem_and_rel
    (fineCandidate input profile).datum _ _).mp hIncident |>.2
  change (finePastedResolution input profile).right.Rel
      ((finePastedResolution input profile).right.repr sheet)
      ((finePastedResolution input profile).newEdge.repr other) at hData
  have hRight : (finePastedResolution input profile).right.Rel sheet
      ((finePastedResolution input profile).newEdge.repr other) :=
    (finePastedResolution input profile).right.rel_repr_right sheet |>.trans hData
  have hWallRepr : (data.vertexPartition wall).Rel sheet
      ((finePastedResolution input profile).newEdge.repr other) := by
    rw [← (data.vertexPartition wall).mem_block_iff,
      ← fine_background_right_block input profile sheet hSheet,
      (finePastedResolution input profile).right.mem_block_iff]
    exact hRight
  have hRefines : (finePastedResolution input profile).newEdge.Refines
      (data.vertexPartition wall) :=
    (finePastedResolution input profile).edge_refines_right.trans
      (LocalResolution.pasteRight_refines (data.vertexPartition wall)
        (fineCandidate input profile).resolution
        (fineCandidate input profile).contracts)
  exact hWallRepr.trans (hRefines.rel
    ((finePastedResolution input profile).newEdge.rel_repr_left other))

theorem coarse_background_new_eq_of_small_source_eq
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hEqual : data.sourceEdge (smallTarget input profile) other =
      data.sourceEdge (smallTarget input profile) sheet) :
    (coarseCandidate input profile).newSourceEdge other =
      (coarseCandidate input profile).newSourceEdge sheet := by
  have hRepr := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  have hFine : (finePartition input profile).Rel sheet other := hRepr.symm
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile).newEdge.repr other =
        (coarsePastedResolution input profile).newEdge.repr sheet
    symm
    apply (coarsePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
    rw [coarse_background_newEdge_block input profile sheet hSheet]
    exact (finePartition input profile).mem_block_iff _ _ |>.mpr hFine

theorem fine_background_new_eq_of_large_source_eq
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet other : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hEqual : data.sourceEdge (largeTarget input profile) other =
      data.sourceEdge (largeTarget input profile) sheet) :
    (fineCandidate input profile).newSourceEdge other =
      (fineCandidate input profile).newSourceEdge sheet := by
  have hRepr := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEqual
  have hLarge : (largePartition input profile).Rel sheet other := hRepr.symm
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (finePastedResolution input profile).newEdge.repr other =
        (finePastedResolution input profile).newEdge.repr sheet
    symm
    apply (finePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
    rw [fine_background_newEdge_block input profile sheet hSheet]
    exact (largePartition input profile).mem_block_iff _ _ |>.mpr hLarge

/-- If the first source survivor is the coarse member's small direction, the
surviving incidences at the fresh background endpoint are exactly the new arm
and the retained second survivor. -/
theorem coarse_background_nonDanglingIncident_right_of_first_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 = smallTarget input profile) :
    nonDanglingIncident (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      {(coarseCandidate input profile).newSourceEdge first.1.1.2,
        (coarseCandidate input profile).oldSourceEdge second.1} := by
  classical
  let candidate := coarseCandidate input profile
  let vertex := data.sourceEndpoint wall sheet
  let firstI : IncidentSourceEdge data vertex := ⟨first.1, hFirst⟩
  let secondI : IncidentSourceEdge data vertex := ⟨second.1, hSecond⟩
  have hPair := survivingIncidences_eq_pair data vertex hNd firstI secondI
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h))) first.2 second.2
  have hTargets := targets_ne_of_ramification_le_one data input.dangling_no_glue
    vertex hNd (by
      have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
          input.distinguishedBlock := by
        intro hEq
        apply hSheet
        have hValue := congrArg Subtype.val hEq
        change (data.vertexPartition wall).repr sheet =
          input.distinguishedBlock.1 at hValue
        change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
          (data.vertexPartition wall).repr sheet
        rw [input.distinguishedBlock.2, hValue]
      change data.localRamification wall
        ((data.vertexPartition wall).toBlock sheet) ≤ 1
      rw [input.localRamification_eq_zero_of_ne hBlockNe]
      omega)
    firstI secondI (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h)))
    first.2 second.2
  have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.1.2 := by
    have hRel := (incident_iff_target_mem_and_rel data first.1 vertex).mp hFirst |>.2
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) first.1.1.2 at hRel
    exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
  have hFirstSheet : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 first.1.1.2 := by
    intro hDist
    exact hSheet (hDist.trans hFirstWall.symm)
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((coarse_old_isDangling_iff input profile old).mpr hDangling)
      obtain ⟨hOldIncident, hOldTarget⟩ :=
        (coarse_background_old_incident_right_iff input profile sheet hSheet old).mp hIncident
      let oldI : IncidentSourceEdge data vertex := ⟨old, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq
        exact (hOldTarget (congrArg (fun e : data.SourceEdge ↦ e.1.1)
          hValue |>.trans hFirstTarget)).elim
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact congrArg candidate.oldSourceEdge
          (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1)
            (Finset.mem_singleton.mp hEq))
    · have hRel := coarse_background_new_incident_right_rel
          input profile sheet other hSheet hIncident
      have hOther : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 other := by
        intro hDist
        exact hSheet (hDist.trans hRel.symm)
      have hOldSurvives := (coarse_background_new_survives_iff_oldSmall
        input profile other hOther).mp hSurvives
      have hOldIncident : Incident data
          (data.sourceEdge (smallTarget input profile) other) vertex := by
        have hBase := incident_sourceEdge_sourceEndpoint data wall
          (smallTarget input profile) (smallTarget_mem input profile) other
        have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall other := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact hRel
        change Incident data (data.sourceEdge (smallTarget input profile) other)
          (data.sourceEndpoint wall sheet)
        rw [hEndpoint]
        exact hBase
      let oldI : IncidentSourceEdge data vertex :=
        ⟨data.sourceEdge (smallTarget input profile) other, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · apply Finset.mem_insert.mpr
        apply Or.inl
        apply coarse_background_new_eq_of_small_source_eq input profile
          first.1.1.2 other hFirstSheet
        have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq
        calc
          data.sourceEdge (smallTarget input profile) other = first.1 := hValue
          _ = data.sourceEdge (smallTarget input profile) first.1.1.2 := by
            rw [← hFirstTarget]
            exact (GluingDatum.sourceEdge_self data first.1).symm
      · have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1)
          (Finset.mem_singleton.mp hEq)
        have hSecondTarget : second.1.1.1 = smallTarget input profile := by
          calc
            second.1.1.1 = (data.sourceEdge (smallTarget input profile) other).1.1 :=
              congrArg (fun e : data.SourceEdge ↦ e.1.1) hValue.symm
            _ = smallTarget input profile := rfl
        exact (hTargets (hFirstTarget.trans hSecondTarget.symm)).elim
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOld
    · rw [hNew]
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨?_, coarse_background_new_incident_right input profile sheet
        first.1.1.2 hSheet hFirstWall⟩
      have hCanonical : data.sourceEdge (smallTarget input profile) first.1.1.2 =
          first.1 := by
        calc
          data.sourceEdge (smallTarget input profile) first.1.1.2 =
              data.sourceEdge first.1.1.1 first.1.1.2 :=
            congrArg (fun targetEdge ↦ data.sourceEdge targetEdge first.1.1.2)
              hFirstTarget.symm
          _ = first.1 := GluingDatum.sourceEdge_self data first.1
      exact (coarse_background_new_survives_iff_oldSmall
        input profile first.1.1.2 hFirstSheet).mpr (by simpa [hCanonical] using first.2)
    · rw [Finset.mem_singleton] at hOld
      rw [hOld]
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨not_isDangling_oldSourceEdge candidate input.valid.1 second.1 second.2, ?_⟩
      apply (coarse_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      exact ⟨hSecond, fun h ↦ hTargets (hFirstTarget.trans h.symm)⟩

theorem coarse_background_retained_eq_of_first_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 = smallTarget input profile) :
    (retainedEdge (coarseCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (coarseCandidate input profile) input.valid.1 second).stablePath := by
  let candidate := coarseCandidate input profile
  have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.1.2 := by
    have hRel := (incident_iff_target_mem_and_rel data first.1 _).mp hFirst |>.2
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) first.1.1.2 at hRel
    exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
  have hFirstSheet : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 first.1.1.2 := by
    intro hDist
    exact hSheet (hDist.trans hFirstWall.symm)
  have hCanonical : data.sourceEdge (smallTarget input profile) first.1.1.2 = first.1 := by
    calc
      data.sourceEdge (smallTarget input profile) first.1.1.2 =
          data.sourceEdge first.1.1.1 first.1.1.2 :=
        congrArg (fun edge ↦ data.sourceEdge edge first.1.1.2) hFirstTarget.symm
      _ = first.1 := GluingDatum.sourceEdge_self data first.1
  have hCanonicalSurvives : ¬ IsDangling data
      (data.sourceEdge (smallTarget input profile) first.1.1.2) := by
    rw [hCanonical]
    exact first.2
  have hNewSurvives : ¬ IsDangling candidate.datum
      (candidate.newSourceEdge first.1.1.2) :=
    (coarse_background_new_survives_iff_oldSmall input profile
      first.1.1.2 hFirstSheet).mpr hCanonicalSurvives
  let new : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge first.1.1.2, hNewSurvives⟩
  have hIncidentNew := coarse_background_new_incident_right input profile sheet
    first.1.1.2 hSheet hFirstWall
  have hTargets := targets_ne_of_ramification_le_one data input.dangling_no_glue
    (data.sourceEndpoint wall sheet) hNd (by
      have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
          input.distinguishedBlock := by
        intro hEq
        apply hSheet
        have hValue := congrArg Subtype.val hEq
        change (data.vertexPartition wall).repr sheet = input.distinguishedBlock.1 at hValue
        change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
          (data.vertexPartition wall).repr sheet
        rw [input.distinguishedBlock.2, hValue]
      change data.localRamification wall ((data.vertexPartition wall).toBlock sheet) ≤ 1
      rw [input.localRamification_eq_zero_of_ne hBlockNe]
      omega)
    ⟨first.1, hFirst⟩ ⟨second.1, hSecond⟩
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data (data.sourceEndpoint wall sheet) ↦ item.1) h)))
    first.2 second.2
  have hIncidentSecond : Incident candidate.datum (candidate.oldSourceEdge second.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (coarse_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      ⟨hSecond, fun h ↦ hTargets (hFirstTarget.trans h.symm)⟩
  have hValency : nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
    rw [← card_nonDanglingIncident,
      coarse_background_nonDanglingIncident_right_of_first_small input profile
        sheet hSheet first second hNe hFirst hSecond hNd hFirstTarget]
    apply Finset.card_pair
    intro hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
    cases hLabels
  have hNewSecond : new.stablePath =
      (retainedEdge candidate input.valid.1 second).stablePath :=
    stablePath_eq_of_consecutive ⟨(by
      intro hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual)
      cases hLabels),
      candidate.datum.sourceEndpoint (freshVertex target) sheet,
      hIncidentNew, hIncidentSecond, hValency⟩
  have hOldNew : (retainedEdge candidate input.valid.1 first).stablePath = new.stablePath := by
    have hPath := coarse_background_new_stablePath_eq_oldSmall input profile
      first.1.1.2 hFirstSheet hCanonicalSurvives
    have hOld : retainedEdge candidate input.valid.1 first =
        (⟨candidate.oldSourceEdge (data.sourceEdge (smallTarget input profile)
          first.1.1.2),
          not_isDangling_oldSourceEdge candidate input.valid.1 _
            hCanonicalSurvives⟩ : NonDanglingEdge candidate.datum) := by
      apply Subtype.ext
      exact congrArg candidate.oldSourceEdge hCanonical.symm
    rw [hOld]
    exact hPath.symm
  exact hOldNew.trans hNewSecond

/-- If neither survivor is the coarse chosen direction, no new background
occurrence survives at the fresh endpoint and the retained old pair is its
complete surviving incidence. -/
theorem coarse_background_nonDanglingIncident_right_of_no_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 ≠ smallTarget input profile)
    (hSecondTarget : second.1.1.1 ≠ smallTarget input profile) :
    nonDanglingIncident (coarseCandidate input profile).datum
        ((coarseCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      {(coarseCandidate input profile).oldSourceEdge first.1,
        (coarseCandidate input profile).oldSourceEdge second.1} := by
  classical
  let candidate := coarseCandidate input profile
  let vertex := data.sourceEndpoint wall sheet
  let firstI : IncidentSourceEdge data vertex := ⟨first.1, hFirst⟩
  let secondI : IncidentSourceEdge data vertex := ⟨second.1, hSecond⟩
  have hPair := survivingIncidences_eq_pair data vertex hNd firstI secondI
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h))) first.2 second.2
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((coarse_old_isDangling_iff input profile old).mpr hDangling)
      have hOldIncident :=
        (coarse_background_old_incident_right_iff input profile sheet hSheet old).mp hIncident |>.1
      let oldI : IncidentSourceEdge data vertex := ⟨old, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · exact Finset.mem_insert.mpr (Or.inl (congrArg candidate.oldSourceEdge
          (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq)))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr
          (congrArg candidate.oldSourceEdge (congrArg
            (fun item : IncidentSourceEdge data vertex ↦ item.1)
            (Finset.mem_singleton.mp hEq))))
    · have hRel := coarse_background_new_incident_right_rel
          input profile sheet other hSheet hIncident
      have hOther : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 other := by
        intro hDist
        exact hSheet (hDist.trans hRel.symm)
      have hOldSurvives := (coarse_background_new_survives_iff_oldSmall
        input profile other hOther).mp hSurvives
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        (smallTarget input profile) (smallTarget_mem input profile) other
      have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall other := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hRel
      have hOldIncident : Incident data (data.sourceEdge (smallTarget input profile) other)
          vertex := by
        change Incident data (data.sourceEdge (smallTarget input profile) other)
          (data.sourceEndpoint wall sheet)
        rw [hEndpoint]
        exact hBase
      let oldI : IncidentSourceEdge data vertex :=
        ⟨data.sourceEdge (smallTarget input profile) other, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · apply (hFirstTarget ?_).elim
        exact (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1.1.1) hEq).symm
      · apply (hSecondTarget ?_).elim
        exact (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1.1.1)
          (Finset.mem_singleton.mp hEq)).symm
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hFirstEq | hSecondEq
    · rw [hFirstEq]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨not_isDangling_oldSourceEdge candidate input.valid.1 first.1 first.2,
          (coarse_background_old_incident_right_iff input profile sheet hSheet first.1).mpr
            ⟨hFirst, hFirstTarget⟩⟩
    · rw [Finset.mem_singleton] at hSecondEq
      rw [hSecondEq]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨not_isDangling_oldSourceEdge candidate input.valid.1 second.1 second.2,
          (coarse_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
            ⟨hSecond, hSecondTarget⟩⟩

theorem coarse_background_retained_eq_of_no_small
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 ≠ smallTarget input profile)
    (hSecondTarget : second.1.1.1 ≠ smallTarget input profile) :
    (retainedEdge (coarseCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (coarseCandidate input profile) input.valid.1 second).stablePath := by
  let candidate := coarseCandidate input profile
  have hFirstIncident : Incident candidate.datum (candidate.oldSourceEdge first.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (coarse_background_old_incident_right_iff input profile sheet hSheet first.1).mpr
      ⟨hFirst, hFirstTarget⟩
  have hSecondIncident : Incident candidate.datum (candidate.oldSourceEdge second.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (coarse_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      ⟨hSecond, hSecondTarget⟩
  have hValency : nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
    rw [← card_nonDanglingIncident,
      coarse_background_nonDanglingIncident_right_of_no_small input profile
        sheet hSheet first second hNe hFirst hSecond hNd hFirstTarget hSecondTarget]
    apply Finset.card_pair
    exact (ResolutionCut.oldSourceEdge_injective candidate).ne
      (fun h ↦ hNe (Subtype.ext h))
  apply stablePath_eq_of_consecutive
  exact ⟨fun h ↦ hNe (retainedEdge_injective candidate input.valid.1 h),
    candidate.datum.sourceEndpoint (freshVertex target) sheet,
    hFirstIncident, hSecondIncident, hValency⟩

/-- The retained-occurrence map for the true coarse member respects every
generating consecutive pair of the old stable-path quotient. -/
theorem coarse_stablePath_retained_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge (coarseCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (coarseCandidate input profile) input.valid.1 second).stablePath := by
  classical
  obtain ⟨hNe, vertex, hFirst, hSecond, hNd⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 vertex.1.2
    · have hSelectedVertex : WallBlock.sourceVertex data wall
          input.distinguishedBlock = vertex :=
        (data.sourceEndpoint_eq_iff wall input.distinguishedBlock.1 vertex).mpr
          ⟨hAt.symm, hSelected⟩
      exact (coarse_retained_selected_eq_anchor input profile first
        (hSelectedVertex.symm ▸ hFirst)).trans
        (coarse_retained_selected_eq_anchor input profile second
          (hSelectedVertex.symm ▸ hSecond)).symm
    · have hFirst' : Incident data first.1 (data.sourceEndpoint wall vertex.1.2) :=
        by rw [hVertex]; exact hFirst
      have hSecond' : Incident data second.1 (data.sourceEndpoint wall vertex.1.2) :=
        by rw [hVertex]; exact hSecond
      have hNd' : nonDanglingValency data (data.sourceEndpoint wall vertex.1.2) = 2 :=
        by rw [hVertex]; exact hNd
      by_cases hFirstTarget : first.1.1.1 = smallTarget input profile
      · exact coarse_background_retained_eq_of_first_small input profile
          vertex.1.2 hSelected first second hNe hFirst' hSecond' hNd' hFirstTarget
      · by_cases hSecondTarget : second.1.1.1 = smallTarget input profile
        · exact (coarse_background_retained_eq_of_first_small input profile
            vertex.1.2 hSelected second first hNe.symm hSecond' hFirst' hNd'
              hSecondTarget).symm
        · exact coarse_background_retained_eq_of_no_small input profile
            vertex.1.2 hSelected first second hNe hFirst' hSecond' hNd'
              hFirstTarget hSecondTarget
  · exact stablePath_eq_of_consecutive (consecutive_retained_of_away
      (coarseCandidate input profile) input.valid
      (coarseCandidate_sourceGenus input profile) first second hNe vertex hAt
      hFirst hSecond hNd)

noncomputable def coarseStablePathLift
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath data → StablePath (coarseCandidate input profile).datum :=
  Quot.lift
    (fun edge ↦ (retainedEdge (coarseCandidate input profile) input.valid.1 edge).stablePath)
    (coarse_stablePath_retained_eq_of_consecutive input profile)

@[simp] theorem coarseStablePathLift_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data) :
    coarseStablePathLift input profile edge.stablePath =
      (retainedEdge (coarseCandidate input profile) input.valid.1 edge).stablePath := rfl

theorem fine_background_nonDanglingIncident_right_of_first_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 = largeTarget input profile) :
    nonDanglingIncident (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      {(fineCandidate input profile).newSourceEdge first.1.1.2,
        (fineCandidate input profile).oldSourceEdge second.1} := by
  classical
  let candidate := fineCandidate input profile
  let vertex := data.sourceEndpoint wall sheet
  let firstI : IncidentSourceEdge data vertex := ⟨first.1, hFirst⟩
  let secondI : IncidentSourceEdge data vertex := ⟨second.1, hSecond⟩
  have hPair := survivingIncidences_eq_pair data vertex hNd firstI secondI
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h))) first.2 second.2
  have hTargets := targets_ne_of_ramification_le_one data input.dangling_no_glue
    vertex hNd (by
      have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
          input.distinguishedBlock := by
        intro hEq
        apply hSheet
        have hValue := congrArg Subtype.val hEq
        change (data.vertexPartition wall).repr sheet =
          input.distinguishedBlock.1 at hValue
        change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
          (data.vertexPartition wall).repr sheet
        rw [input.distinguishedBlock.2, hValue]
      change data.localRamification wall
        ((data.vertexPartition wall).toBlock sheet) ≤ 1
      rw [input.localRamification_eq_zero_of_ne hBlockNe]
      omega)
    firstI secondI (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h)))
    first.2 second.2
  have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.1.2 := by
    have hRel := (incident_iff_target_mem_and_rel data first.1 vertex).mp hFirst |>.2
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) first.1.1.2 at hRel
    exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
  have hFirstSheet : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 first.1.1.2 := by
    intro hDist
    exact hSheet (hDist.trans hFirstWall.symm)
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((fine_old_isDangling_iff input profile old).mpr hDangling)
      obtain ⟨hOldIncident, hOldTarget⟩ :=
        (fine_background_old_incident_right_iff input profile sheet hSheet old).mp hIncident
      let oldI : IncidentSourceEdge data vertex := ⟨old, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq
        exact (hOldTarget (congrArg (fun e : data.SourceEdge ↦ e.1.1)
          hValue |>.trans hFirstTarget)).elim
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact congrArg candidate.oldSourceEdge
          (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1)
            (Finset.mem_singleton.mp hEq))
    · have hRel := fine_background_new_incident_right_rel
          input profile sheet other hSheet hIncident
      have hOther : ¬(data.vertexPartition wall).Rel
          input.distinguishedBlock.1 other := by
        intro hDist
        exact hSheet (hDist.trans hRel.symm)
      have hOldSurvives := (fine_background_new_survives_iff_oldLarge
        input profile other hOther).mp hSurvives
      have hOldIncident : Incident data
          (data.sourceEdge (largeTarget input profile) other) vertex := by
        have hBase := incident_sourceEdge_sourceEndpoint data wall
          (largeTarget input profile) (largeTarget_mem input profile) other
        have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall other := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact hRel
        change Incident data (data.sourceEdge (largeTarget input profile) other)
          (data.sourceEndpoint wall sheet)
        rw [hEndpoint]
        exact hBase
      let oldI : IncidentSourceEdge data vertex :=
        ⟨data.sourceEdge (largeTarget input profile) other, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · apply Finset.mem_insert.mpr
        apply Or.inl
        apply fine_background_new_eq_of_large_source_eq input profile
          first.1.1.2 other hFirstSheet
        have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq
        calc
          data.sourceEdge (largeTarget input profile) other = first.1 := hValue
          _ = data.sourceEdge (largeTarget input profile) first.1.1.2 := by
            rw [← hFirstTarget]
            exact (GluingDatum.sourceEdge_self data first.1).symm
      · have hValue := congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1)
          (Finset.mem_singleton.mp hEq)
        have hSecondTarget : second.1.1.1 = largeTarget input profile := by
          calc
            second.1.1.1 = (data.sourceEdge (largeTarget input profile) other).1.1 :=
              congrArg (fun e : data.SourceEdge ↦ e.1.1) hValue.symm
            _ = largeTarget input profile := rfl
        exact (hTargets (hFirstTarget.trans hSecondTarget.symm)).elim
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOld
    · rw [hNew]
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨?_, fine_background_new_incident_right input profile sheet
        first.1.1.2 hSheet hFirstWall⟩
      have hCanonical : data.sourceEdge (largeTarget input profile) first.1.1.2 =
          first.1 := by
        calc
          data.sourceEdge (largeTarget input profile) first.1.1.2 =
              data.sourceEdge first.1.1.1 first.1.1.2 :=
            congrArg (fun targetEdge ↦ data.sourceEdge targetEdge first.1.1.2)
              hFirstTarget.symm
          _ = first.1 := GluingDatum.sourceEdge_self data first.1
      exact (fine_background_new_survives_iff_oldLarge
        input profile first.1.1.2 hFirstSheet).mpr (by simpa [hCanonical] using first.2)
    · rw [Finset.mem_singleton] at hOld
      rw [hOld]
      apply (mem_nonDanglingIncident _ _ _).mpr
      refine ⟨not_isDangling_oldSourceEdge candidate input.valid.1 second.1 second.2, ?_⟩
      apply (fine_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      exact ⟨hSecond, fun h ↦ hTargets (hFirstTarget.trans h.symm)⟩

theorem fine_background_retained_eq_of_first_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 = largeTarget input profile) :
    (retainedEdge (fineCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (fineCandidate input profile) input.valid.1 second).stablePath := by
  let candidate := fineCandidate input profile
  have hFirstWall : (data.vertexPartition wall).Rel sheet first.1.1.2 := by
    have hRel := (incident_iff_target_mem_and_rel data first.1 _).mp hFirst |>.2
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr sheet) first.1.1.2 at hRel
    exact (data.vertexPartition wall).rel_repr_right sheet |>.trans hRel
  have hFirstSheet : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 first.1.1.2 := by
    intro hDist
    exact hSheet (hDist.trans hFirstWall.symm)
  have hCanonical : data.sourceEdge (largeTarget input profile) first.1.1.2 = first.1 := by
    calc
      data.sourceEdge (largeTarget input profile) first.1.1.2 =
          data.sourceEdge first.1.1.1 first.1.1.2 :=
        congrArg (fun edge ↦ data.sourceEdge edge first.1.1.2) hFirstTarget.symm
      _ = first.1 := GluingDatum.sourceEdge_self data first.1
  have hCanonicalSurvives : ¬ IsDangling data
      (data.sourceEdge (largeTarget input profile) first.1.1.2) := by
    rw [hCanonical]
    exact first.2
  have hNewSurvives : ¬ IsDangling candidate.datum
      (candidate.newSourceEdge first.1.1.2) :=
    (fine_background_new_survives_iff_oldLarge input profile
      first.1.1.2 hFirstSheet).mpr hCanonicalSurvives
  let new : NonDanglingEdge candidate.datum :=
    ⟨candidate.newSourceEdge first.1.1.2, hNewSurvives⟩
  have hIncidentNew := fine_background_new_incident_right input profile sheet
    first.1.1.2 hSheet hFirstWall
  have hTargets := targets_ne_of_ramification_le_one data input.dangling_no_glue
    (data.sourceEndpoint wall sheet) hNd (by
      have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
          input.distinguishedBlock := by
        intro hEq
        apply hSheet
        have hValue := congrArg Subtype.val hEq
        change (data.vertexPartition wall).repr sheet = input.distinguishedBlock.1 at hValue
        change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
          (data.vertexPartition wall).repr sheet
        rw [input.distinguishedBlock.2, hValue]
      change data.localRamification wall ((data.vertexPartition wall).toBlock sheet) ≤ 1
      rw [input.localRamification_eq_zero_of_ne hBlockNe]
      omega)
    ⟨first.1, hFirst⟩ ⟨second.1, hSecond⟩
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data (data.sourceEndpoint wall sheet) ↦ item.1) h)))
    first.2 second.2
  have hIncidentSecond : Incident candidate.datum (candidate.oldSourceEdge second.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (fine_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      ⟨hSecond, fun h ↦ hTargets (hFirstTarget.trans h.symm)⟩
  have hValency : nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
    rw [← card_nonDanglingIncident,
      fine_background_nonDanglingIncident_right_of_first_large input profile
        sheet hSheet first second hNe hFirst hSecond hNd hFirstTarget]
    apply Finset.card_pair
    intro hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
    cases hLabels
  have hNewSecond : new.stablePath =
      (retainedEdge candidate input.valid.1 second).stablePath :=
    stablePath_eq_of_consecutive ⟨(by
      intro hEqual
      have hLabels := (occurrenceEquiv target wall candidate.right).injective
        (congrArg (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual)
      cases hLabels),
      candidate.datum.sourceEndpoint (freshVertex target) sheet,
      hIncidentNew, hIncidentSecond, hValency⟩
  have hOldNew : (retainedEdge candidate input.valid.1 first).stablePath = new.stablePath := by
    have hPath := fine_background_new_stablePath_eq_oldLarge input profile
      first.1.1.2 hFirstSheet hCanonicalSurvives
    have hOld : retainedEdge candidate input.valid.1 first =
        (⟨candidate.oldSourceEdge (data.sourceEdge (largeTarget input profile)
          first.1.1.2),
          not_isDangling_oldSourceEdge candidate input.valid.1 _
            hCanonicalSurvives⟩ : NonDanglingEdge candidate.datum) := by
      apply Subtype.ext
      exact congrArg candidate.oldSourceEdge hCanonical.symm
    rw [hOld]
    exact hPath.symm
  exact hOldNew.trans hNewSecond

/-- If neither survivor is the fine chosen direction, no new background
occurrence survives at the fresh endpoint and the retained old pair is its
complete surviving incidence. -/
theorem fine_background_nonDanglingIncident_right_of_no_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 ≠ largeTarget input profile)
    (hSecondTarget : second.1.1.1 ≠ largeTarget input profile) :
    nonDanglingIncident (fineCandidate input profile).datum
        ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target) sheet) =
      {(fineCandidate input profile).oldSourceEdge first.1,
        (fineCandidate input profile).oldSourceEdge second.1} := by
  classical
  let candidate := fineCandidate input profile
  let vertex := data.sourceEndpoint wall sheet
  let firstI : IncidentSourceEdge data vertex := ⟨first.1, hFirst⟩
  let secondI : IncidentSourceEdge data vertex := ⟨second.1, hSecond⟩
  have hPair := survivingIncidences_eq_pair data vertex hNd firstI secondI
    (fun h ↦ hNe (Subtype.ext (congrArg
      (fun item : IncidentSourceEdge data vertex ↦ item.1) h))) first.2 second.2
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases sourceEdge_cases candidate edge with ⟨old, rfl⟩ | ⟨other, rfl⟩
    · have hOldSurvives : ¬ IsDangling data old := by
        intro hDangling
        exact hSurvives ((fine_old_isDangling_iff input profile old).mpr hDangling)
      have hOldIncident :=
        (fine_background_old_incident_right_iff input profile sheet hSheet old).mp hIncident |>.1
      let oldI : IncidentSourceEdge data vertex := ⟨old, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · exact Finset.mem_insert.mpr (Or.inl (congrArg candidate.oldSourceEdge
          (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1) hEq)))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr
          (congrArg candidate.oldSourceEdge (congrArg
            (fun item : IncidentSourceEdge data vertex ↦ item.1)
            (Finset.mem_singleton.mp hEq))))
    · have hRel := fine_background_new_incident_right_rel
          input profile sheet other hSheet hIncident
      have hOther : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 other := by
        intro hDist
        exact hSheet (hDist.trans hRel.symm)
      have hOldSurvives := (fine_background_new_survives_iff_oldLarge
        input profile other hOther).mp hSurvives
      have hBase := incident_sourceEdge_sourceEndpoint data wall
        (largeTarget input profile) (largeTarget_mem input profile) other
      have hEndpoint : data.sourceEndpoint wall sheet = data.sourceEndpoint wall other := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hRel
      have hOldIncident : Incident data (data.sourceEdge (largeTarget input profile) other)
          vertex := by
        change Incident data (data.sourceEdge (largeTarget input profile) other)
          (data.sourceEndpoint wall sheet)
        rw [hEndpoint]
        exact hBase
      let oldI : IncidentSourceEdge data vertex :=
        ⟨data.sourceEdge (largeTarget input profile) other, hOldIncident⟩
      have hOldMem : oldI ∈
          (Finset.univ.filter fun item : IncidentSourceEdge data vertex ↦
            ¬ IsDangling data item.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOldSurvives⟩
      rw [hPair] at hOldMem
      rcases Finset.mem_insert.mp hOldMem with hEq | hEq
      · apply (hFirstTarget ?_).elim
        exact (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1.1.1) hEq).symm
      · apply (hSecondTarget ?_).elim
        exact (congrArg (fun item : IncidentSourceEdge data vertex ↦ item.1.1.1)
          (Finset.mem_singleton.mp hEq)).symm
  · intro hMem
    rcases Finset.mem_insert.mp hMem with hFirstEq | hSecondEq
    · rw [hFirstEq]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨not_isDangling_oldSourceEdge candidate input.valid.1 first.1 first.2,
          (fine_background_old_incident_right_iff input profile sheet hSheet first.1).mpr
            ⟨hFirst, hFirstTarget⟩⟩
    · rw [Finset.mem_singleton] at hSecondEq
      rw [hSecondEq]
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨not_isDangling_oldSourceEdge candidate input.valid.1 second.1 second.2,
          (fine_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
            ⟨hSecond, hSecondTarget⟩⟩

theorem fine_background_retained_eq_of_no_large
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hNd : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2)
    (hFirstTarget : first.1.1.1 ≠ largeTarget input profile)
    (hSecondTarget : second.1.1.1 ≠ largeTarget input profile) :
    (retainedEdge (fineCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (fineCandidate input profile) input.valid.1 second).stablePath := by
  let candidate := fineCandidate input profile
  have hFirstIncident : Incident candidate.datum (candidate.oldSourceEdge first.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (fine_background_old_incident_right_iff input profile sheet hSheet first.1).mpr
      ⟨hFirst, hFirstTarget⟩
  have hSecondIncident : Incident candidate.datum (candidate.oldSourceEdge second.1)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
    (fine_background_old_incident_right_iff input profile sheet hSheet second.1).mpr
      ⟨hSecond, hSecondTarget⟩
  have hValency : nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 := by
    rw [← card_nonDanglingIncident,
      fine_background_nonDanglingIncident_right_of_no_large input profile
        sheet hSheet first second hNe hFirst hSecond hNd hFirstTarget hSecondTarget]
    apply Finset.card_pair
    exact (ResolutionCut.oldSourceEdge_injective candidate).ne
      (fun h ↦ hNe (Subtype.ext h))
  apply stablePath_eq_of_consecutive
  exact ⟨fun h ↦ hNe (retainedEdge_injective candidate input.valid.1 h),
    candidate.datum.sourceEndpoint (freshVertex target) sheet,
    hFirstIncident, hSecondIncident, hValency⟩

/-- The retained-occurrence map for the true fine member respects every
generating consecutive pair of the old stable-path quotient. -/
theorem fine_stablePath_retained_eq_of_consecutive
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge (fineCandidate input profile) input.valid.1 first).stablePath =
      (retainedEdge (fineCandidate input profile) input.valid.1 second).stablePath := by
  classical
  obtain ⟨hNe, vertex, hFirst, hSecond, hNd⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 vertex.1.2
    · have hSelectedVertex : WallBlock.sourceVertex data wall
          input.distinguishedBlock = vertex :=
        (data.sourceEndpoint_eq_iff wall input.distinguishedBlock.1 vertex).mpr
          ⟨hAt.symm, hSelected⟩
      exact (fine_retained_selected_eq_anchor input profile first
        (hSelectedVertex.symm ▸ hFirst)).trans
        (fine_retained_selected_eq_anchor input profile second
          (hSelectedVertex.symm ▸ hSecond)).symm
    · have hFirst' : Incident data first.1 (data.sourceEndpoint wall vertex.1.2) :=
        by rw [hVertex]; exact hFirst
      have hSecond' : Incident data second.1 (data.sourceEndpoint wall vertex.1.2) :=
        by rw [hVertex]; exact hSecond
      have hNd' : nonDanglingValency data (data.sourceEndpoint wall vertex.1.2) = 2 :=
        by rw [hVertex]; exact hNd
      by_cases hFirstTarget : first.1.1.1 = largeTarget input profile
      · exact fine_background_retained_eq_of_first_large input profile
          vertex.1.2 hSelected first second hNe hFirst' hSecond' hNd' hFirstTarget
      · by_cases hSecondTarget : second.1.1.1 = largeTarget input profile
        · exact (fine_background_retained_eq_of_first_large input profile
            vertex.1.2 hSelected second first hNe.symm hSecond' hFirst' hNd'
              hSecondTarget).symm
        · exact fine_background_retained_eq_of_no_large input profile
            vertex.1.2 hSelected first second hNe hFirst' hSecond' hNd'
              hFirstTarget hSecondTarget
  · exact stablePath_eq_of_consecutive (consecutive_retained_of_away
      (fineCandidate input profile) input.valid
      (fineCandidate_sourceGenus input profile) first second hNe vertex hAt
      hFirst hSecond hNd)

noncomputable def fineStablePathLift
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    StablePath data → StablePath (fineCandidate input profile).datum :=
  Quot.lift
    (fun edge ↦ (retainedEdge (fineCandidate input profile) input.valid.1 edge).stablePath)
    (fine_stablePath_retained_eq_of_consecutive input profile)

@[simp] theorem fineStablePathLift_mk
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge data) :
        fineStablePathLift input profile edge.stablePath =
      (retainedEdge (fineCandidate input profile) input.valid.1 edge).stablePath := rfl

theorem coarse_exists_retained_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (coarseCandidate input profile).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (coarseCandidate input profile) input.valid.1 old).stablePath =
        edge.stablePath := by
  let candidate := coarseCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (coarseCandidate_sourceGenus input profile) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet
    · refine ⟨⟨profile.small.1, profile.small_survives⟩, ?_⟩
      have hNew := coarse_newSourceEdge_eq_of_selected input profile sheet hSelected
      have hEdge : (⟨candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge candidate.datum) = coarseAnchorNew input profile :=
        Subtype.ext hNew
      rw [hEdge]
      exact (coarse_anchor_new_stablePath_eq_small input profile).symm
    · obtain ⟨hOld, hPath⟩ := coarse_background_new_has_oldSmall_row
        input profile sheet hSelected hSurvives
      refine ⟨⟨data.sourceEdge (smallTarget input profile) sheet, hOld⟩, ?_⟩
      exact hPath.symm

theorem coarseStablePathLift_surjective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Surjective (coarseStablePathLift input profile) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := coarse_exists_retained_row input profile edge
      exact ⟨old.stablePath, hPath⟩

/-- A surviving fine new occurrence on the distinguished block is the
anchor occurrence; the only other fine block there is the proved dangling
residual singleton. -/
theorem fine_selected_new_eq_anchor_of_survives
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSurvives : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) :
    (fineCandidate input profile).newSourceEdge sheet =
      (fineCandidate input profile).newSourceEdge (anchor input profile) := by
  have hWallMem : sheet ∈ (data.vertexPartition wall).block (anchor input profile) :=
    (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      ((anchor_wall_rel input profile).symm.trans hSelected)
  rw [← fine_blocks_cover_wall input profile] at hWallMem
  rcases Finset.mem_union.mp hWallMem with hResidual | hAnchor
  · have hFineRel := (finePartition input profile).mem_block_iff _ _ |>.mp hResidual
    have hNewEq : (fineCandidate input profile).newSourceEdge sheet =
        (fineCandidate input profile).newSourceEdge (residualSheet input profile) := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (finePastedResolution input profile).newEdge.repr sheet =
            (finePastedResolution input profile).newEdge.repr (residualSheet input profile)
        apply (finePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
        rw [pasted_newEdge_block_selected input profile
          sheet hSelected]
        exact (finePartition input profile).mem_block_iff _ _ |>.mpr hFineRel.symm
    apply (hSurvives ?_).elim
    rw [hNewEq]
    exact fine_residual_new_dangles input profile
  · have hFineRel := (finePartition input profile).mem_block_iff _ _ |>.mp hAnchor
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (finePastedResolution input profile).newEdge.repr sheet =
          (finePastedResolution input profile).newEdge.repr (anchor input profile)
      apply (finePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
      rw [pasted_newEdge_block_selected input profile
        sheet hSelected]
      exact (finePartition input profile).mem_block_iff _ _ |>.mpr hFineRel.symm

theorem fine_exists_retained_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (edge : NonDanglingEdge (fineCandidate input profile).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (fineCandidate input profile) input.valid.1 old).stablePath =
        edge.stablePath := by
  let candidate := fineCandidate input profile
  rcases nonDanglingEdge_cases candidate input.valid
      (fineCandidate_sourceGenus input profile) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · by_cases hSelected : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet
    · refine ⟨⟨profile.large.1, profile.large_survives⟩, ?_⟩
      have hNew := fine_selected_new_eq_anchor_of_survives input profile
        sheet hSelected hSurvives
      have hEdge : (⟨candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge candidate.datum) = fineAnchorNew input profile :=
        Subtype.ext hNew
      rw [hEdge]
      exact (fine_anchor_new_stablePath_eq_large input profile).symm
    · obtain ⟨hOld, hPath⟩ := fine_background_new_has_oldLarge_row
        input profile sheet hSelected hSurvives
      refine ⟨⟨data.sourceEdge (largeTarget input profile) sheet, hOld⟩, ?_⟩
      exact hPath.symm

theorem fineStablePathLift_surjective
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Function.Surjective (fineStablePathLift input profile) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := fine_exists_retained_row input profile edge
      exact ⟨old.stablePath, hPath⟩

end DraismaVargas.LocalCases.W3Nd2StableLift
