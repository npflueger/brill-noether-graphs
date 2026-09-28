import DraismaVargas.LocalCases.W3Nd2Survival

/-!
# Background rows for the true Figure 31 candidates

Figure 31 is Case {w3-r1-nd2} of Draisma--Vargas Part I.
Away from the distinguished wall block, each candidate uses a fine resolution
whose divalent endpoint and new edge carry the same exterior edge partition.
Thus each background source vertex on that side has exactly the retained old
occurrence and the corresponding new occurrence.  If the old occurrence
survives, connectedness forbids the new one from being its sole dangling
companion, so the pair is consecutive and has one stable row.
-/

namespace DraismaVargas.LocalCases.W3Nd2Background

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival ResolutionM11 ResolutionM1k
open ResolutionCoarseFine ResolutionSurvival M11SplitRows

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

theorem coarseCandidate_resolution_background (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile).resolution sheet =
      fineResolution (data.vertexPartition wall) (finePartition input profile)
        (fine_refines_wall input profile) := by
  change LocalResolution.onBlock (data.vertexPartition wall) (anchor input profile)
      (thirdResolution (data.vertexPartition wall)) _ sheet = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ (by
    intro hAnchor
    exact hSheet ((anchor_wall_rel input profile).trans hAnchor))]
  rfl

theorem fineCandidate_resolution_background (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile).resolution sheet =
      fineResolution (data.vertexPartition wall) (largePartition input profile)
        (large_refines_wall input profile) := by
  change LocalResolution.onBlock (data.vertexPartition wall) (anchor input profile)
      (selectedResolution input profile) (fineBackground input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ (by
    intro hAnchor
    exact hSheet ((anchor_wall_rel input profile).trans hAnchor))]
  rfl

theorem coarse_background_left_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).left.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem coarse_background_newEdge_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).newEdge.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_left_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).left.block sheet =
      (largePartition input profile).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem fine_background_newEdge_block (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).newEdge.block sheet =
      (largePartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_background input profile
    ((data.vertexPartition wall).repr sheet) (by
      intro hDist
      exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem coarse_background_left_card_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Fintype.card (IncidentSourceEdge (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet)) = 2 := by
  classical
  let candidate := coarseCandidate input profile
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = 2
  rw [coarse_left_target_incident_pair]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right (some (smallTarget input profile)) :=
    (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (coarsePastedResolution input profile).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (coarsePastedResolution input profile).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right (some (smallTarget input profile))) =
      finePartition input profile :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  rw [SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile).left.rel_repr_left sheet),
    SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile).left.rel_repr_left sheet)]
  have hRepr : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      ((data.vertexPartition wall).repr sheet) := by
    intro hDist
    exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hNewCount : (coarsePastedResolution input profile).newEdge.blockCountWithin
      (coarsePastedResolution input profile).left sheet = 1 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left,
      coarseCandidate_resolution_background input profile _ hRepr]
    exact SheetPartition.blockCountWithin_self _ _
  have hOldCount : (finePartition input profile).blockCountWithin
      (coarsePastedResolution input profile).left sheet = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [coarse_background_left_block input profile sheet hSheet]
    exact SheetPartition.blockCountWithin_self _ _
  rw [hNewCount, hOldCount]

theorem fine_background_left_card_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Fintype.card (IncidentSourceEdge (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet)) = 2 := by
  classical
  let candidate := fineCandidate input profile
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = 2
  rw [fine_left_target_incident_pair]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right (some (largeTarget input profile)) :=
    (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (finePastedResolution input profile).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (finePastedResolution input profile).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right (some (largeTarget input profile))) =
      largePartition input profile :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  rw [SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile).left.rel_repr_left sheet),
    SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile).left.rel_repr_left sheet)]
  have hRepr : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1
      ((data.vertexPartition wall).repr sheet) := by
    intro hDist
    exact hSheet (hDist.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hNewCount : (finePastedResolution input profile).newEdge.blockCountWithin
      (finePastedResolution input profile).left sheet = 1 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left,
      fineCandidate_resolution_background input profile _ hRepr]
    exact SheetPartition.blockCountWithin_self _ _
  have hOldCount : (largePartition input profile).blockCountWithin
      (finePastedResolution input profile).left sheet = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [fine_background_left_block input profile sheet hSheet]
    exact SheetPartition.blockCountWithin_self _ _
  rw [hNewCount, hOldCount]

/-- At a connected source vertex with exactly two incidences, either both
occurrences survive pruning or both dangle. -/
theorem survives_iff_of_card_two (datum : GluingDatum target degree)
    (hConnected : datum.Connected) (vertex : datum.SourceVertex)
    (first second : datum.SourceEdge)
    (hFirstIncident : Incident datum first vertex)
    (hSecondIncident : Incident datum second vertex)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    (¬ IsDangling datum first) ↔ ¬ IsDangling datum second := by
  classical
  have force_other : ∀ survivor other : datum.SourceEdge,
      Incident datum survivor vertex → Incident datum other vertex →
      ¬ IsDangling datum survivor → ¬ IsDangling datum other := by
    intro survivor other hSurvivorIncident hOtherIncident hSurvivor hOther
    let dangling : IncidentSourceEdge datum vertex := ⟨other, hOtherIncident⟩
    have hDanglingPositive : 0 <
        ((Finset.univ : Finset (IncidentSourceEdge datum vertex)).filter
          (fun edge ↦ IsDangling datum edge.1)).card :=
      Finset.card_pos.mpr ⟨dangling,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOther⟩⟩
    have hSurvivingPositive :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident datum
        hSurvivor hSurvivorIncident
    have hNotOne := NonDanglingValency.nonDanglingValency_ne_one datum
      hConnected vertex
    have hTotal := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (IncidentSourceEdge datum vertex)))
      (p := fun edge ↦ IsDangling datum edge.1)
    rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
      hCard] at hTotal
    omega
  exact ⟨force_other first second hFirstIncident hSecondIncident,
    force_other second first hSecondIncident hFirstIncident⟩

theorem coarse_background_new_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile).right (coarsePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile).exterior) sheet))

theorem coarse_background_oldSmall_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge
        (data.sourceEdge (smallTarget input profile) sheet))
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet) := by
  apply oldSourceEdge_incident_old
  · exact smallTarget_mem input profile
  · change rightOf (smallTarget input profile) (smallTarget input profile) = false
    simp [rightOf]

theorem fine_background_new_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (fineCandidate input profile).right (finePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (fineCandidate input profile).exterior) sheet))

theorem fine_background_oldLarge_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge
        (data.sourceEdge (largeTarget input profile) sheet))
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        sheet) := by
  apply oldSourceEdge_incident_old
  · exact largeTarget_mem input profile
  · change rightOf (largeTarget input profile) (largeTarget input profile) = false
    simp [rightOf]

theorem coarse_background_new_survives_iff_oldSmall
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (¬ IsDangling (coarseCandidate input profile).datum
        ((coarseCandidate input profile).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (smallTarget input profile) sheet) := by
  let candidate := coarseCandidate input profile
  have hPair := survives_iff_of_card_two candidate.datum
    (coarseCandidate_valid input profile).1
    (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
    (candidate.newSourceEdge sheet)
    (candidate.oldSourceEdge (data.sourceEdge (smallTarget input profile) sheet))
    (coarse_background_new_incident_left input profile sheet)
    (coarse_background_oldSmall_incident_left input profile sheet)
    (coarse_background_left_card_two input profile sheet hSheet)
  exact hPair.trans (not_congr (coarse_old_isDangling_iff input profile _))

theorem fine_background_new_survives_iff_oldLarge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (¬ IsDangling (fineCandidate input profile).datum
        ((fineCandidate input profile).newSourceEdge sheet)) ↔
      ¬ IsDangling data (data.sourceEdge (largeTarget input profile) sheet) := by
  let candidate := fineCandidate input profile
  have hPair := survives_iff_of_card_two candidate.datum
    (fineCandidate_valid input profile).1
    (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
    (candidate.newSourceEdge sheet)
    (candidate.oldSourceEdge (data.sourceEdge (largeTarget input profile) sheet))
    (fine_background_new_incident_left input profile sheet)
    (fine_background_oldLarge_incident_left input profile sheet)
    (fine_background_left_card_two input profile sheet hSheet)
  exact hPair.trans (not_congr (fine_old_isDangling_iff input profile _))

theorem nonDanglingValency_eq_two_of_card_two_of_survives
    (datum : GluingDatum target degree) (hConnected : datum.Connected)
    (vertex : datum.SourceVertex) (edge : datum.SourceEdge)
    (hIncident : Incident datum edge vertex) (hSurvives : ¬ IsDangling datum edge)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    nonDanglingValency datum vertex = 2 := by
  classical
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    datum hSurvives hIncident
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one datum hConnected vertex
  have hLe : nonDanglingValency datum vertex ≤
      Fintype.card (IncidentSourceEdge datum vertex) := by
    rw [← card_filter_not_isDangling_eq_nonDanglingValency, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem coarse_background_new_consecutive_oldSmall
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (smallTarget input profile) sheet)) :
    Consecutive (coarseCandidate input profile).datum
      ⟨(coarseCandidate input profile).newSourceEdge sheet,
        (coarse_background_new_survives_iff_oldSmall input profile sheet hSheet).2 hOld⟩
      ⟨(coarseCandidate input profile).oldSourceEdge
          (data.sourceEdge (smallTarget input profile) sheet),
        ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let candidate := coarseCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) sheet
  refine ⟨?_, vertex, coarse_background_new_incident_left input profile sheet,
    coarse_background_oldSmall_incident_left input profile sheet, ?_⟩
  · intro hEqual
    have hTargets := congrArg
      (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact nonDanglingValency_eq_two_of_card_two_of_survives candidate.datum
      (coarseCandidate_valid input profile).1 vertex
      (candidate.newSourceEdge sheet)
      (coarse_background_new_incident_left input profile sheet)
      ((coarse_background_new_survives_iff_oldSmall input profile sheet hSheet).2 hOld)
      (coarse_background_left_card_two input profile sheet hSheet)

theorem fine_background_new_consecutive_oldLarge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (largeTarget input profile) sheet)) :
    Consecutive (fineCandidate input profile).datum
      ⟨(fineCandidate input profile).newSourceEdge sheet,
        (fine_background_new_survives_iff_oldLarge input profile sheet hSheet).2 hOld⟩
      ⟨(fineCandidate input profile).oldSourceEdge
          (data.sourceEdge (largeTarget input profile) sheet),
        ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall) sheet
  refine ⟨?_, vertex, fine_background_new_incident_left input profile sheet,
    fine_background_oldLarge_incident_left input profile sheet, ?_⟩
  · intro hEqual
    have hTargets := congrArg
      (fun edge : NonDanglingEdge candidate.datum ↦ edge.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact nonDanglingValency_eq_two_of_card_two_of_survives candidate.datum
      (fineCandidate_valid input profile).1 vertex
      (candidate.newSourceEdge sheet)
      (fine_background_new_incident_left input profile sheet)
      ((fine_background_new_survives_iff_oldLarge input profile sheet hSheet).2 hOld)
      (fine_background_left_card_two input profile sheet hSheet)

theorem coarse_background_new_stablePath_eq_oldSmall
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (smallTarget input profile) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(coarseCandidate input profile).newSourceEdge sheet,
          (coarse_background_new_survives_iff_oldSmall input profile sheet hSheet).2 hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(coarseCandidate input profile).oldSourceEdge
            (data.sourceEdge (smallTarget input profile) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ :=
  stablePath_eq_of_consecutive
    (coarse_background_new_consecutive_oldSmall input profile sheet hSheet hOld)

theorem fine_background_new_stablePath_eq_oldLarge
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hOld : ¬ IsDangling data (data.sourceEdge (largeTarget input profile) sheet)) :
    NonDanglingEdge.stablePath
        ⟨(fineCandidate input profile).newSourceEdge sheet,
          (fine_background_new_survives_iff_oldLarge input profile sheet hSheet).2 hOld⟩ =
      NonDanglingEdge.stablePath
        ⟨(fineCandidate input profile).oldSourceEdge
            (data.sourceEdge (largeTarget input profile) sheet),
          ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ :=
  stablePath_eq_of_consecutive
    (fine_background_new_consecutive_oldLarge input profile sheet hSheet hOld)

/-- Every surviving coarse background new occurrence has the retained old
small-direction occurrence as a stable-row representative. -/
theorem coarse_background_new_has_oldSmall_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNew : ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (smallTarget input profile) sheet),
      NonDanglingEdge.stablePath
          ⟨(coarseCandidate input profile).newSourceEdge sheet, hNew⟩ =
        NonDanglingEdge.stablePath
          ⟨(coarseCandidate input profile).oldSourceEdge
              (data.sourceEdge (smallTarget input profile) sheet),
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let hOld := (coarse_background_new_survives_iff_oldSmall
    input profile sheet hSheet).1 hNew
  refine ⟨hOld, ?_⟩
  simpa only using coarse_background_new_stablePath_eq_oldSmall
    input profile sheet hSheet hOld

/-- Every surviving fine background new occurrence has the retained old
large-direction occurrence as a stable-row representative. -/
theorem fine_background_new_has_oldLarge_row
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNew : ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge sheet)) :
    ∃ hOld : ¬ IsDangling data (data.sourceEdge (largeTarget input profile) sheet),
      NonDanglingEdge.stablePath
          ⟨(fineCandidate input profile).newSourceEdge sheet, hNew⟩ =
        NonDanglingEdge.stablePath
          ⟨(fineCandidate input profile).oldSourceEdge
              (data.sourceEdge (largeTarget input profile) sheet),
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ hOld⟩ := by
  let hOld := (fine_background_new_survives_iff_oldLarge
    input profile sheet hSheet).1 hNew
  refine ⟨hOld, ?_⟩
  simpa only using fine_background_new_stablePath_eq_oldLarge
    input profile sheet hSheet hOld

end DraismaVargas.LocalCases.W3Nd2Background
