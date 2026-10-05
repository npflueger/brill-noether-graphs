module

public import DraismaVargas.LocalCases.W3Nd2FineCandidates
public import DraismaVargas.LocalCases.M11SplitSurvival
public import DraismaVargas.LocalCases.ResolutionPruning

@[expose] public section

/-!
# Selected-block survival for the two Figure 31 W3 nd2 candidates

The true fine candidate has two selected new occurrences: the singleton
residual occurrence dangles, while the size-`k` occurrence survives and meets
the retained large direction in one stable row.  The coarse candidate has one
selected new occurrence across the whole wall block; it survives and meets the
retained small direction in one stable row.  All statements below use literal
source incidences and derive pruning through genus preservation.
-/

namespace DraismaVargas.LocalCases.W3Nd2Survival

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates ResolutionM11 ResolutionPruning ResolutionSurvival
open M11SplitSurvival M11SplitRows M11SourceCandidates ResolutionM1k

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

theorem coarse_old_isDangling_iff (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (edge : data.SourceEdge) :
    IsDangling (coarseCandidate input profile).datum
        ((coarseCandidate input profile).oldSourceEdge edge) ↔ IsDangling data edge :=
  isDangling_oldSourceEdge_iff _ input.valid (coarseCandidate_sourceGenus input profile) edge

theorem fine_old_isDangling_iff (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (edge : data.SourceEdge) :
    IsDangling (fineCandidate input profile).datum
        ((fineCandidate input profile).oldSourceEdge edge) ↔ IsDangling data edge :=
  isDangling_oldSourceEdge_iff _ input.valid (fineCandidate_sourceGenus input profile) edge

theorem coarse_small_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge profile.small.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.small_survives

theorem coarse_large_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge profile.large.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.large_survives

theorem fine_small_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge profile.small.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.small_survives

theorem fine_large_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge profile.large.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.large_survives

/-- The wall block contains a sheet outside the small survivor's size-`k`
edge block. -/
theorem exists_residualSheet (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ∃ sheet, sheet ∈ (data.vertexPartition wall).block (anchor input profile) ∧
      sheet ∉ (finePartition input profile).block (anchor input profile) := by
  apply Finset.exists_mem_notMem_of_card_lt_card
  change (finePartition input profile).blockCard (anchor input profile) <
    (data.vertexPartition wall).blockCard (anchor input profile)
  have hFine : (finePartition input profile).blockCard (anchor input profile) =
      data.sourceEdgeIndex profile.small.1 := rfl
  rw [hFine]
  have hWall := SheetPartition.blockCard_congr (data.vertexPartition wall)
    (anchor_wall_rel input profile)
  have hIndex := profile.small_index
  omega

/-- The unique residual sheet outside the small survivor's size-`k` block. -/
noncomputable def residualSheet (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : Fin degree :=
  Classical.choose (exists_residualSheet input profile)

theorem residualSheet_wall_mem (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    residualSheet input profile ∈
      (data.vertexPartition wall).block (anchor input profile) :=
  (Classical.choose_spec (exists_residualSheet input profile)).1

theorem residualSheet_fine_not_mem (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    residualSheet input profile ∉ (finePartition input profile).block (anchor input profile) :=
  (Classical.choose_spec (exists_residualSheet input profile)).2

theorem residualSheet_wall_rel (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (residualSheet input profile) := by
  have hAnchor : (data.vertexPartition wall).Rel (anchor input profile)
      (residualSheet input profile) :=
    ((data.vertexPartition wall).mem_block_iff _ _).mp
      (residualSheet_wall_mem input profile)
  exact (anchor_wall_rel input profile).trans hAnchor

theorem residualSheet_fine_separate (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬(finePartition input profile).Rel (anchor input profile)
      (residualSheet input profile) := fun h ↦
  residualSheet_fine_not_mem input profile
    ((finePartition input profile).mem_block_iff _ _ |>.mpr h)

theorem residual_fine_blockCard_eq_one (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (finePartition input profile).blockCard (residualSheet input profile) = 1 := by
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let anchorSheet := anchor input profile
  let residual := residualSheet input profile
  have hFineSubset : fine.block residual ⊆ coarse.block anchorSheet := by
    intro sheet hSheet
    have hFineRel := (fine.mem_block_iff residual sheet).mp hSheet
    have hCoarseResidual : coarse.Rel anchorSheet residual :=
      (coarse.mem_block_iff anchorSheet residual).mp (residualSheet_wall_mem input profile)
    exact (coarse.mem_block_iff anchorSheet sheet).mpr
      (hCoarseResidual.trans ((fine_refines_wall input profile).rel hFineRel))
  have hDisjoint : Disjoint (fine.block residual) (fine.block anchorSheet) := by
    apply Finset.disjoint_left.mpr
    intro sheet hResidual hAnchor
    have hOne := (fine.mem_block_iff residual sheet).mp hResidual
    have hTwo := (fine.mem_block_iff anchorSheet sheet).mp hAnchor
    exact residualSheet_fine_separate input profile (hTwo.trans hOne.symm)
  have hUnionSubset : fine.block residual ∪ fine.block anchorSheet ⊆ coarse.block anchorSheet := by
    intro sheet hSheet
    rcases Finset.mem_union.mp hSheet with hResidual | hAnchor
    · exact hFineSubset hResidual
    · exact (coarse.mem_block_iff anchorSheet sheet).mpr
        ((fine_refines_wall input profile).rel ((fine.mem_block_iff anchorSheet sheet).mp hAnchor))
  have hCardLe := Finset.card_le_card hUnionSubset
  rw [Finset.card_union_of_disjoint hDisjoint,
    show (fine.block anchorSheet).card = (geometry input profile).k by
      exact (geometry input profile).fineCard,
    show (coarse.block anchorSheet).card = (geometry input profile).k + 1 by
      exact (geometry input profile).wallCard] at hCardLe
  have hPos := fine.blockCard_pos residual
  change 0 < (fine.block residual).card at hPos
  change (fine.block residual).card = 1
  omega

theorem fine_blockCountWithin_eq_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (finePartition input profile).blockCountWithin (data.vertexPartition wall)
      (anchor input profile) = 2 := by
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let residual := residualSheet input profile
  have hNe : fine.repr (anchor input profile) ≠ fine.repr residual := by
    intro h
    exact residualSheet_fine_separate input profile h
  have hPair : ({fine.repr (anchor input profile), fine.repr residual} :
      Finset (Fin degree)) ⊆ (coarse.block (anchor input profile)).image fine.repr := by
    intro item hItem
    rcases Finset.mem_insert.mp hItem with hAnchor | hResidual
    · subst item
      exact Finset.mem_image.mpr ⟨anchor input profile, coarse.self_mem_block _, rfl⟩
    · rw [Finset.mem_singleton] at hResidual
      subst item
      exact Finset.mem_image.mpr
        ⟨residual, residualSheet_wall_mem input profile, rfl⟩
  have hLower := Finset.card_le_card hPair
  rw [Finset.card_pair hNe] at hLower
  have hUpper := fine_blockCountWithin_le_two input profile (anchor input profile)
    (anchor_wall_rel input profile)
  exact Nat.le_antisymm hUpper hLower

theorem large_blockCountWithin_wall_eq_one (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (largePartition input profile).blockCountWithin (data.vertexPartition wall)
      (anchor input profile) = 1 := by
  let large := largePartition input profile
  let coarse := data.vertexPartition wall
  let largeSheet := profile.large.1.1.2
  unfold SheetPartition.blockCountWithin
  have hBlock : coarse.block (anchor input profile) = large.block largeSheet := by
    calc
      coarse.block (anchor input profile) = coarse.block input.distinguishedBlock.1 :=
        coarse.block_eq_of_rel (anchor_wall_rel input profile).symm
      _ = large.block largeSheet := (large_block_eq_wall input profile).symm
  rw [hBlock]
  exact large.blockCountWithin_self largeSheet

theorem fine_blocks_cover_wall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (finePartition input profile).block (residualSheet input profile) ∪
        (finePartition input profile).block (anchor input profile) =
      (data.vertexPartition wall).block (anchor input profile) := by
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let residual := residualSheet input profile
  have hResidualSubset : fine.block residual ⊆ coarse.block (anchor input profile) := by
    intro sheet hSheet
    have hRel := (fine.mem_block_iff residual sheet).mp hSheet
    exact (coarse.mem_block_iff (anchor input profile) sheet).mpr
      ((coarse.mem_block_iff (anchor input profile) residual).mp
        (residualSheet_wall_mem input profile) |>.trans
          ((fine_refines_wall input profile).rel hRel))
  have hAnchorSubset : fine.block (anchor input profile) ⊆
      coarse.block (anchor input profile) := by
    intro sheet hSheet
    exact (coarse.mem_block_iff (anchor input profile) sheet).mpr
      ((fine_refines_wall input profile).rel
        ((fine.mem_block_iff (anchor input profile) sheet).mp hSheet))
  have hSubset : fine.block residual ∪ fine.block (anchor input profile) ⊆
      coarse.block (anchor input profile) := Finset.union_subset hResidualSubset hAnchorSubset
  have hDisjoint : Disjoint (fine.block residual) (fine.block (anchor input profile)) := by
    apply Finset.disjoint_left.mpr
    intro sheet hResidual hAnchor
    exact residualSheet_fine_separate input profile
      (((fine.mem_block_iff (anchor input profile) sheet).mp hAnchor).trans
        ((fine.mem_block_iff residual sheet).mp hResidual).symm)
  apply Finset.eq_of_subset_of_card_le hSubset
  rw [Finset.card_union_of_disjoint hDisjoint]
  change coarse.blockCard (anchor input profile) ≤
    fine.blockCard residual + fine.blockCard (anchor input profile)
  rw [residual_fine_blockCard_eq_one input profile,
    show fine.blockCard (anchor input profile) = (geometry input profile).k by
      exact (geometry input profile).fineCard,
    show coarse.blockCard (anchor input profile) = (geometry input profile).k + 1 by
      exact (geometry input profile).wallCard]
  omega

theorem selectedFine_blockCountWithin_wall_eq_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedFine input profile).blockCountWithin (data.vertexPartition wall)
      (anchor input profile) = 2 := by
  classical
  let selected := selectedFine input profile
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let residual := residualSheet input profile
  unfold SheetPartition.blockCountWithin
  have hImage : (coarse.block (anchor input profile)).image selected.repr =
      {selected.repr (anchor input profile), selected.repr residual} := by
    ext item
    constructor
    · intro hItem
      obtain ⟨sheet, hSheet, hValue⟩ := Finset.mem_image.mp hItem
      rw [← hValue]
      rw [← fine_blocks_cover_wall input profile] at hSheet
      rcases Finset.mem_union.mp hSheet with hResidual | hAnchor
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton.mpr
        exact (selectedFine_rel_iff_of_selected input profile
          (residualSheet_wall_rel input profile)).mpr
            ((fine.mem_block_iff residual sheet).mp hResidual) |>.symm
      · apply Finset.mem_insert.mpr
        exact Or.inl (((selectedFine_rel_iff_of_selected input profile
          (anchor_wall_rel input profile)).mpr
            ((fine.mem_block_iff (anchor input profile) sheet).mp hAnchor)).symm)
    · intro hItem
      rcases Finset.mem_insert.mp hItem with hAnchor | hResidual
      · exact Finset.mem_image.mpr
          ⟨anchor input profile, coarse.self_mem_block _, hAnchor.symm⟩
      · rw [Finset.mem_singleton] at hResidual
        exact Finset.mem_image.mpr
          ⟨residual, residualSheet_wall_mem input profile, hResidual.symm⟩
  rw [hImage, Finset.card_pair]
  intro hEqual
  apply residualSheet_fine_separate input profile
  apply (selectedFine_rel_iff_of_selected input profile
    (anchor_wall_rel input profile)).mp
  exact hEqual

theorem residual_small_source_isDangling (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    IsDangling data (data.sourceEdge (smallTarget input profile) (residualSheet input profile)) := by
  have hAt := smallTarget_mem input profile
  have hRefines := fine_refines_wall input profile
  have hEdgeRel := hRefines.rel
    ((finePartition input profile).rel_repr_right (residualSheet input profile))
  have hIncident : Incident data
      (data.sourceEdge (smallTarget input profile) (residualSheet input profile))
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
    apply (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock _).mpr
    refine ⟨hAt, Subtype.ext ?_⟩
    exact hEdgeRel.symm.trans ((residualSheet_wall_rel input profile).symm.trans
      input.distinguishedBlock.2)
  by_contra hSurvives
  let incident : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
    ⟨data.sourceEdge (smallTarget input profile) (residualSheet input profile), hIncident⟩
  have hMem := (mem_survivors data input.distinguishedBlock incident).mpr hSurvives
  rw [profile.surviving] at hMem
  rcases Finset.mem_insert.mp hMem with hSmall | hLarge
  · have hSheet := congrArg
      (fun item : IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
        item.1.1.2) hSmall
    apply residualSheet_fine_separate input profile
    change (finePartition input profile).repr (anchor input profile) =
      (finePartition input profile).repr (residualSheet input profile)
    exact profile.small.1.2.trans hSheet.symm
  · have hTarget := congrArg
      (fun item : IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
        item.1.1.1) (Finset.mem_singleton.mp hLarge)
    exact profile.target_ne hTarget

/-- At a source vertex with three actual incidences, two dangling incidences
force the third to dangle as well: otherwise it would be the unique survivor. -/
theorem dangling_of_card_three_of_two_dangling
    (datum : GluingDatum target degree) (hConnected : datum.Connected)
    (vertex : datum.SourceVertex)
    (first second other : IncidentSourceEdge datum vertex)
    (hFirst : IsDangling datum first.1) (hSecond : IsDangling datum second.1)
    (hNe : first ≠ second)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 3) :
    IsDangling datum other.1 := by
  classical
  by_contra hOther
  have hPair : ({first, second} : Finset (IncidentSourceEdge datum vertex)) ⊆
      Finset.univ.filter (fun edge ↦ IsDangling datum edge.1) := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirst⟩
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecond⟩
  have hTwo : 2 ≤ ((Finset.univ : Finset (IncidentSourceEdge datum vertex)).filter
      fun edge ↦ IsDangling datum edge.1).card := by
    simpa [hNe] using Finset.card_le_card hPair
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    datum hOther other.2
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one datum hConnected vertex
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge datum vertex)))
    (p := fun edge ↦ IsDangling datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ, hCard] at hTotal
  omega

theorem fine_residual_right_blockCard_one (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ((fineCandidate input profile).datum.vertexPartition (freshVertex target)).blockCard
      (residualSheet input profile) = 1 := by
  change (finePastedResolution input profile).right.blockCard
    (residualSheet input profile) = 1
  rw [pasted_right_blockCard_selected input profile _
    (residualSheet_wall_rel input profile), residual_fine_blockCard_eq_one]

theorem fine_residual_right_card_three (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Fintype.card (IncidentSourceEdge (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (freshVertex target)
        (residualSheet input profile))) = 3 := by
  apply (card_incident_sourceEndpoint_of_blockCard_one _ _ _
    (fine_residual_right_blockCard_one input profile)).trans
  have hTarget := (candidate_target_valencies (fineCandidate input profile)).2
  change (GluingDatum.incidentEdges
    (target := graph target wall (fineCandidate input profile).right)
      (freshVertex target)).card = 3 at hTarget
  exact hTarget

theorem fine_residual_oldSmall_dangles (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile))) :=
  (fine_old_isDangling_iff input profile _).mpr
    (residual_small_source_isDangling input profile)

theorem fine_residual_oldThird_dangles (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge
        (thirdSourceEdge input profile (residualSheet input profile))) :=
  (fine_old_isDangling_iff input profile _).mpr
    (thirdSourceEdge_isDangling input profile _ (residualSheet_wall_rel input profile))

/-- The residual singleton new occurrence dangles at the selected fine
trivalent endpoint: its two old companions already dangle. -/
theorem fine_residual_new_dangles (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (residualSheet input profile)) := by
  let candidate := fineCandidate input profile
  let sheet := residualSheet input profile
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  have hSmallRight : candidate.right (smallTarget input profile) = true := by
    change rightOf (largeTarget input profile) (smallTarget input profile) = true
    simp [rightOf, profile.target_ne]
  have hThirdRight : candidate.right (thirdTarget input profile) = true := by
    change rightOf (largeTarget input profile) (thirdTarget input profile) = true
    simp [rightOf, thirdTarget_ne_large input profile]
  have hSmallIncident : Incident candidate.datum
      (candidate.oldSourceEdge (data.sourceEdge (smallTarget input profile) sheet)) vertex :=
    oldSourceEdge_incident_fresh candidate _ (smallTarget_mem input profile) hSmallRight sheet
  have hThirdIncident : Incident candidate.datum
      (candidate.oldSourceEdge (thirdSourceEdge input profile sheet)) vertex := by
    have h := oldSourceEdge_incident_fresh candidate (thirdTarget input profile)
      (thirdTarget_mem input profile) hThirdRight sheet
    simpa only [thirdSourceEdge] using h
  have hNewIncident : Incident candidate.datum (candidate.newSourceEdge sheet) vertex :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      candidate.right (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))
  apply dangling_of_card_three_of_two_dangling candidate.datum
    (fineCandidate_valid input profile).1 vertex
    ⟨candidate.oldSourceEdge (data.sourceEdge (smallTarget input profile) sheet), hSmallIncident⟩
    ⟨candidate.oldSourceEdge (thirdSourceEdge input profile sheet), hThirdIncident⟩
    ⟨candidate.newSourceEdge sheet, hNewIncident⟩
    (fine_residual_oldSmall_dangles input profile)
    (fine_residual_oldThird_dangles input profile)
  · intro hEq
    have hTargets := congrArg
      (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEq
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    exact thirdTarget_ne_small input profile (Option.some.inj hLabels).symm
  · exact fine_residual_right_card_three input profile

theorem oldSourceEdge_incident_old
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hRight : candidate.right edge = false) (sheet : Fin degree) :
    Incident candidate.datum (candidate.oldSourceEdge (data.sourceEdge edge sheet))
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
  have hAtUp : occurrenceEquiv target wall candidate.right (some edge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (oldVertex target wall) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hAt ⊢
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_oldVertex_iff target wall candidate.right edge).mpr
      ⟨hAt, hRight⟩
  have hIncident := incident_sourceEdge_sourceEndpoint candidate.datum
    (oldVertex target wall)
    (occurrenceEquiv target wall candidate.right (some edge)) hAtUp sheet
  have hEq : candidate.datum.sourceEdge
      (occurrenceEquiv target wall candidate.right (some edge)) sheet =
      candidate.oldSourceEdge (data.sourceEdge edge sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) edge sheet
  exact hEq ▸ hIncident

theorem fine_left_target_incident_pair (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    GluingDatum.incidentEdges
        (target := graph target wall (fineCandidate input profile).right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall (fineCandidate input profile).right none,
        occurrenceEquiv target wall (fineCandidate input profile).right
          (some (largeTarget input profile))} := by
  classical
  let candidate := fineCandidate input profile
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact Or.inl rfl
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some]
      apply (oldEnds_incident_oldVertex_iff target wall candidate.right
        (largeTarget input profile)).mpr
      refine ⟨?_, ?_⟩
      · simpa only [GluingDatum.incidentEdges, Finset.mem_filter,
          Finset.mem_univ, true_and] using largeTarget_mem input profile
      change rightOf (largeTarget input profile) (largeTarget input profile) = false
      simp [rightOf]
  · have hNe : occurrenceEquiv target wall candidate.right none ≠
        occurrenceEquiv target wall candidate.right
          (some (largeTarget input profile)) := by
      exact (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
    rw [Finset.card_pair hNe]
    exact le_of_eq (candidate_target_valencies candidate).1

theorem fine_left_card_three (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Fintype.card (IncidentSourceEdge (fineCandidate input profile).datum
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile))) = 3 := by
  classical
  let candidate := fineCandidate input profile
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr
        (anchor input profile))) = 3
  rw [fine_left_target_incident_pair]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right
        (some (largeTarget input profile)) := by
    exact (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (finePastedResolution input profile).left := by
    exact GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (finePastedResolution input profile).newEdge := by
    exact GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right
        (some (largeTarget input profile))) =
      data.edgePartition (largeTarget input profile) := by
    exact GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  change (finePastedResolution input profile).newEdge.blockCountWithin
      (finePastedResolution input profile).left
      ((finePastedResolution input profile).left.repr (anchor input profile)) +
    (data.edgePartition (largeTarget input profile)).blockCountWithin
      (finePastedResolution input profile).left
      ((finePastedResolution input profile).left.repr (anchor input profile)) = 3
  rw [SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile).left.rel_repr_left
        (anchor input profile)),
    SheetPartition.blockCountWithin_congr _ _
      ((finePastedResolution input profile).left.rel_repr_left
        (anchor input profile))]
  have hNew : (finePastedResolution input profile).newEdge.blockCountWithin
      (finePastedResolution input profile).left (anchor input profile) = 2 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left]
    rw [fineCandidate_resolution_selected input profile
      ((data.vertexPartition wall).repr (anchor input profile))
      ((anchor_wall_rel input profile).trans
        ((data.vertexPartition wall).rel_repr_right (anchor input profile)))]
    change (selectedFine input profile).blockCountWithin
      (data.vertexPartition wall) (anchor input profile) = 2
    exact selectedFine_blockCountWithin_wall_eq_two input profile
  have hLarge : (data.edgePartition (largeTarget input profile)).blockCountWithin
      (finePastedResolution input profile).left (anchor input profile) = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [pasted_left_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile)]
    exact large_blockCountWithin_wall_eq_one input profile
  rw [hNew, hLarge]

theorem fine_left_endpoint_eq_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) first =
      (fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((fineCandidate input profile).datum.vertexPartition
        (oldVertex target wall)).repr first =
      ((fineCandidate input profile).datum.vertexPartition
        (oldVertex target wall)).repr second
    have hVertex : (fineCandidate input profile).datum.vertexPartition
        (oldVertex target wall) = (finePastedResolution input profile).left := by
      exact GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex]
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← pasted_left_block_selected input profile first hFirst] at hMem
    exact ((finePastedResolution input profile).left.mem_block_iff first second).mp hMem

theorem fine_anchor_new_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (anchor input profile))
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (fineCandidate input profile).right (finePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (fineCandidate input profile).exterior) (anchor input profile)))

theorem fine_residual_new_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (residualSheet input profile))
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) := by
  have hIncident : Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (residualSheet input profile))
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (residualSheet input profile)) :=
    Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
      (fineCandidate input profile).right (finePastedResolution input profile)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (fineCandidate input profile).exterior) (residualSheet input profile)))
  exact fine_left_endpoint_eq_of_wall_rel input profile (anchor input profile)
    (residualSheet input profile) (anchor_wall_rel input profile)
    ((anchor_wall_rel input profile).symm.trans
      (residualSheet_wall_rel input profile)) ▸ hIncident

theorem fine_large_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (fineCandidate input profile).datum
      ((fineCandidate input profile).oldSourceEdge profile.large.1)
      ((fineCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) := by
  let candidate := fineCandidate input profile
  have hRight : candidate.right (largeTarget input profile) = false := by
    change rightOf (largeTarget input profile) (largeTarget input profile) = false
    simp [rightOf]
  have hIncident : Incident candidate.datum
      (candidate.oldSourceEdge (data.sourceEdge (largeTarget input profile)
        profile.large.1.1.2))
      (candidate.datum.sourceEndpoint (oldVertex target wall)
        profile.large.1.1.2) :=
    oldSourceEdge_incident_old candidate _ (largeTarget_mem input profile)
      hRight profile.large.1.1.2
  have hWallLarge : (data.vertexPartition wall).Rel (anchor input profile)
      profile.large.1.1.2 := by
    have hMem : profile.large.1.1.2 ∈
        (data.vertexPartition wall).block input.distinguishedBlock.1 := by
      rw [← large_block_eq_wall input profile]
      exact (data.edgePartition (largeTarget input profile)).self_mem_block _
    exact (anchor_wall_rel input profile).symm.trans
      (((data.vertexPartition wall).mem_block_iff _ _).mp hMem)
  have hEndpoint := fine_left_endpoint_eq_of_wall_rel input profile
    (anchor input profile) profile.large.1.1.2
    (anchor_wall_rel input profile) hWallLarge
  rw [hEndpoint]
  simpa only [GluingDatum.sourceEdge_self] using hIncident

theorem fine_anchor_new_ne_residual (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineCandidate input profile).newSourceEdge (anchor input profile) ≠
      (fineCandidate input profile).newSourceEdge (residualSheet input profile) := by
  intro hEqual
  have hSheets := congrArg
    (fun edge : (fineCandidate input profile).datum.SourceEdge ↦ edge.1.2) hEqual
  apply residualSheet_fine_separate input profile
  have hNewRel : (finePastedResolution input profile).newEdge.Rel
      (anchor input profile) (residualSheet input profile) := hSheets
  have hMem := ((finePastedResolution input profile).newEdge.mem_block_iff
    (anchor input profile) (residualSheet input profile)).mpr hNewRel
  rw [pasted_newEdge_block_selected input profile (anchor input profile)
    (anchor_wall_rel input profile)] at hMem
  exact ((finePartition input profile).mem_block_iff _ _).mp hMem

/-- The size-`k` fine-block new occurrence survives.  The other selected new
occurrence dangles, while the retained large occurrence supplies a survivor
at their common trivalent source vertex. -/
theorem fine_anchor_new_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (fineCandidate input profile).datum
      ((fineCandidate input profile).newSourceEdge (anchor input profile)) := by
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall)
    (anchor input profile)
  apply survives_of_trivalent_of_deleted candidate.datum
    (fineCandidate_valid input profile).1 vertex
    ⟨candidate.oldSourceEdge profile.large.1, fine_large_incident_left input profile⟩
    ⟨candidate.newSourceEdge (residualSheet input profile),
      fine_residual_new_incident_left input profile⟩
    ⟨candidate.newSourceEdge (anchor input profile),
      fine_anchor_new_incident_left input profile⟩
    (fine_large_survives input profile) (fine_residual_new_dangles input profile)
  · intro hEqual
    apply fine_anchor_new_ne_residual input profile
    exact (congrArg (fun edge : IncidentSourceEdge candidate.datum vertex ↦ edge.1)
      hEqual).symm
  · exact fine_left_card_three input profile

noncomputable def fineAnchorNew (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (fineCandidate input profile).datum :=
  ⟨(fineCandidate input profile).newSourceEdge (anchor input profile),
    fine_anchor_new_survives input profile⟩

noncomputable def fineRetainedLarge (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (fineCandidate input profile).datum :=
  ⟨(fineCandidate input profile).oldSourceEdge profile.large.1,
    fine_large_survives input profile⟩

/-- At the divalent-side source vertex, the surviving selected new edge has
the same stable row as the old large survivor. -/
theorem fine_anchor_new_stablePath_eq_large (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineAnchorNew input profile).stablePath =
      (fineRetainedLarge input profile).stablePath := by
  let candidate := fineCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall)
    (anchor input profile)
  apply stablePath_eq_of_trivalent_deleted candidate.datum
    (fineCandidate_valid input profile).1 _ _ vertex
    (fine_anchor_new_incident_left input profile)
    (fine_large_incident_left input profile)
    ⟨candidate.newSourceEdge (residualSheet input profile),
      fine_residual_new_incident_left input profile⟩
    (fine_residual_new_dangles input profile)
    (fine_left_card_three input profile)

theorem coarseCandidate_resolution_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile).resolution sheet =
      thirdResolution (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall) (anchor input profile)
      (thirdResolution (data.vertexPartition wall)) _ sheet = _
  rw [LocalResolution.onBlock_of_rel]
  exact (anchor_wall_rel input profile).symm.trans hSheet

noncomputable abbrev coarsePastedResolution (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall)
    (coarseCandidate input profile).resolution (coarseCandidate input profile).contracts

theorem coarse_pasted_left_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem coarse_pasted_right_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem coarse_pasted_newEdge_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile).newEdge.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (coarseCandidate input profile).resolution
    (coarseCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem coarse_newSourceEdge_eq_of_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile).newSourceEdge sheet =
      (coarseCandidate input profile).newSourceEdge (anchor input profile) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (coarsePastedResolution input profile).newEdge.repr sheet =
      (coarsePastedResolution input profile).newEdge.repr (anchor input profile)
    apply (coarsePastedResolution input profile).newEdge.mem_block_iff _ _ |>.mp
    rw [coarse_pasted_newEdge_block_selected input profile sheet hSheet]
    exact (data.vertexPartition wall).mem_block_iff _ _ |>.mpr
      (hSheet.symm.trans (anchor_wall_rel input profile))

theorem coarse_left_target_incident_pair (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    GluingDatum.incidentEdges
        (target := graph target wall (coarseCandidate input profile).right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall (coarseCandidate input profile).right none,
        occurrenceEquiv target wall (coarseCandidate input profile).right
          (some (smallTarget input profile))} := by
  classical
  let candidate := coarseCandidate input profile
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact Or.inl rfl
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some]
      apply (oldEnds_incident_oldVertex_iff target wall candidate.right
        (smallTarget input profile)).mpr
      refine ⟨?_, ?_⟩
      · simpa only [GluingDatum.incidentEdges, Finset.mem_filter,
          Finset.mem_univ, true_and] using smallTarget_mem input profile
      · change rightOf (smallTarget input profile) (smallTarget input profile) = false
        simp [rightOf]
  · have hNe : occurrenceEquiv target wall candidate.right none ≠
        occurrenceEquiv target wall candidate.right
          (some (smallTarget input profile)) :=
      (occurrenceEquiv target wall candidate.right).injective.ne (by simp)
    rw [Finset.card_pair hNe]
    exact le_of_eq (candidate_target_valencies candidate).1

theorem coarse_left_card_three (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Fintype.card (IncidentSourceEdge (coarseCandidate input profile).datum
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile))) = 3 := by
  classical
  let candidate := coarseCandidate input profile
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr
        (anchor input profile))) = 3
  rw [coarse_left_target_incident_pair]
  have hNe : occurrenceEquiv target wall candidate.right none ≠
      occurrenceEquiv target wall candidate.right
        (some (smallTarget input profile)) :=
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
      data.edgePartition (smallTarget input profile) :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld]
  change (coarsePastedResolution input profile).newEdge.blockCountWithin
      (coarsePastedResolution input profile).left
      ((coarsePastedResolution input profile).left.repr (anchor input profile)) +
    (finePartition input profile).blockCountWithin
      (coarsePastedResolution input profile).left
      ((coarsePastedResolution input profile).left.repr (anchor input profile)) = 3
  rw [SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile).left.rel_repr_left
        (anchor input profile)),
    SheetPartition.blockCountWithin_congr _ _
      ((coarsePastedResolution input profile).left.rel_repr_left
        (anchor input profile))]
  have hNewCount : (coarsePastedResolution input profile).newEdge.blockCountWithin
      (coarsePastedResolution input profile).left (anchor input profile) = 1 := by
    rw [LocalResolution.paste_newEdge_blockCountWithin_left]
    rw [coarseCandidate_resolution_selected input profile
      ((data.vertexPartition wall).repr (anchor input profile))
      ((anchor_wall_rel input profile).trans
        ((data.vertexPartition wall).rel_repr_right (anchor input profile)))]
    exact SheetPartition.blockCountWithin_self _ _
  have hSmallCount : (finePartition input profile).blockCountWithin
      (coarsePastedResolution input profile).left (anchor input profile) = 2 := by
    unfold SheetPartition.blockCountWithin
    rw [coarse_pasted_left_block_selected input profile (anchor input profile)
      (anchor_wall_rel input profile)]
    exact fine_blockCountWithin_eq_two input profile
  rw [hNewCount, hSmallCount]

theorem coarse_left_endpoint_eq_of_wall_rel (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    (coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) first =
      (coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((coarseCandidate input profile).datum.vertexPartition
        (oldVertex target wall)).repr first =
      ((coarseCandidate input profile).datum.vertexPartition
        (oldVertex target wall)).repr second
    have hVertex : (coarseCandidate input profile).datum.vertexPartition
        (oldVertex target wall) = (coarsePastedResolution input profile).left :=
      GlobalResolution.expandedVertexPartition_old_wall data wall _
    rw [hVertex]
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← coarse_pasted_left_block_selected input profile first hFirst] at hMem
    exact ((coarsePastedResolution input profile).left.mem_block_iff first second).mp hMem

theorem coarse_anchor_new_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge (anchor input profile))
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    (coarseCandidate input profile).right (coarsePastedResolution input profile)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (coarseCandidate input profile).exterior) (anchor input profile)))

theorem coarse_small_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge profile.small.1)
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) := by
  let candidate := coarseCandidate input profile
  have hRight : candidate.right (smallTarget input profile) = false := by
    change rightOf (smallTarget input profile) (smallTarget input profile) = false
    simp [rightOf]
  simpa only [GluingDatum.sourceEdge_self] using
    oldSourceEdge_incident_old candidate _ (smallTarget_mem input profile)
      hRight (anchor input profile)

theorem coarse_residual_oldSmall_incident_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Incident (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile)))
      ((coarseCandidate input profile).datum.sourceEndpoint (oldVertex target wall)
        (anchor input profile)) := by
  let candidate := coarseCandidate input profile
  have hRight : candidate.right (smallTarget input profile) = false := by
    change rightOf (smallTarget input profile) (smallTarget input profile) = false
    simp [rightOf]
  have hIncident := oldSourceEdge_incident_old candidate _
    (smallTarget_mem input profile) hRight (residualSheet input profile)
  have hEndpoint := coarse_left_endpoint_eq_of_wall_rel input profile
    (anchor input profile) (residualSheet input profile)
    (anchor_wall_rel input profile)
    ((anchor_wall_rel input profile).symm.trans
      (residualSheet_wall_rel input profile))
  rw [hEndpoint]
  exact hIncident

theorem coarse_residual_oldSmall_dangles (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile))) :=
  (coarse_old_isDangling_iff input profile _).mpr
    (residual_small_source_isDangling input profile)

/-- The coarse selected new occurrence is forced to survive by the retained
small occurrence and a dangling residual small occurrence at their common
trivalent source vertex. -/
theorem coarse_anchor_new_survives (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    ¬ IsDangling (coarseCandidate input profile).datum
      ((coarseCandidate input profile).newSourceEdge (anchor input profile)) := by
  let candidate := coarseCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall)
    (anchor input profile)
  apply survives_of_trivalent_of_deleted candidate.datum
    (coarseCandidate_valid input profile).1 vertex
    ⟨candidate.oldSourceEdge profile.small.1, coarse_small_incident_left input profile⟩
    ⟨candidate.oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile)),
      coarse_residual_oldSmall_incident_left input profile⟩
    ⟨candidate.newSourceEdge (anchor input profile),
      coarse_anchor_new_incident_left input profile⟩
    (coarse_small_survives input profile)
    (coarse_residual_oldSmall_dangles input profile)
  · intro hEqual
    have hTargets := congrArg
      (fun edge : IncidentSourceEdge candidate.datum vertex ↦ edge.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact coarse_left_card_three input profile

noncomputable def coarseAnchorNew (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (coarseCandidate input profile).datum :=
  ⟨(coarseCandidate input profile).newSourceEdge (anchor input profile),
    coarse_anchor_new_survives input profile⟩

noncomputable def coarseRetainedSmall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    NonDanglingEdge (coarseCandidate input profile).datum :=
  ⟨(coarseCandidate input profile).oldSourceEdge profile.small.1,
    coarse_small_survives input profile⟩

/-- The coarse selected new edge inherits the stable row of the old small
survivor at its left endpoint. -/
theorem coarse_anchor_new_stablePath_eq_small (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (coarseAnchorNew input profile).stablePath =
      (coarseRetainedSmall input profile).stablePath := by
  let candidate := coarseCandidate input profile
  let vertex := candidate.datum.sourceEndpoint (oldVertex target wall)
    (anchor input profile)
  apply stablePath_eq_of_trivalent_deleted candidate.datum
    (coarseCandidate_valid input profile).1 _ _ vertex
    (coarse_anchor_new_incident_left input profile)
    (coarse_small_incident_left input profile)
    ⟨candidate.oldSourceEdge
        (data.sourceEdge (smallTarget input profile) (residualSheet input profile)),
      coarse_residual_oldSmall_incident_left input profile⟩
    (coarse_residual_oldSmall_dangles input profile)
    (coarse_left_card_three input profile)

end DraismaVargas.LocalCases.W3Nd2Survival
