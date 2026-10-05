module

public import DraismaVargas.LocalCases.M11SplitLimitMatrix

@[expose] public section

/-!
# The actual first-split branch vertex

The trivalent vertex replacing the old distinguished wall block is the fresh
vertex on the third survivor's sheet. Its three surviving incidences are the
retained third occurrence, the same-sheet double occurrence, and the new arm.
This is an endpoint census, not an arbitrary stable-row labelling.
-/

namespace DraismaVargas.LocalCases.M11SplitBranch

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties
open M11SourceCandidates M11SplitSurvival M11SplitRows M11SplitLeaves

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

noncomputable abbrev branchVertex : (firstSplitPattern input profile hCard).candidate.datum.SourceVertex :=
  (firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
    (freshVertex target) profile.third.1.1.2

noncomputable def branchDouble : NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge profile.doubleLabel) profile.third.1.1.2,
    double_sourceEdge_survives profile hCard _ (sheet_rel_of_incident_block profile.third)⟩

include hCard in
theorem third_sheet_ne_deleted : profile.third.1.1.2 ≠ profile.deleted.edge.1.1.2 := by
  intro hEq
  have hEdge : profile.third.1 = profile.deleted.edge.1 := by
    apply Subtype.ext
    exact Prod.ext (profile.third_target.trans (deleted_target_eq_single profile hCard).symm) hEq
  exact profile.third_survives (hEdge ▸ profile.deleted.dangling)

noncomputable def branchEdges : Finset (firstSplitPattern input profile hCard).candidate.datum.SourceEdge := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  exact {candidate.newSourceEdge profile.third.1.1.2,
    candidate.oldSourceEdge profile.third.1, candidate.oldSourceEdge (branchDouble profile hCard).1}

private theorem old_ne_new (old : data.SourceEdge) (sheet : Fin degree) :
    (firstSplitPattern input profile hCard).candidate.oldSourceEdge old ≠
      (firstSplitPattern input profile hCard).candidate.newSourceEdge sheet := by
  intro hEq
  have hLabels := (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right).injective
    (congrArg (fun edge ↦ edge.1.1) hEq)
  cases hLabels

private theorem third_ne_double : profile.third.1 ≠ (branchDouble profile hCard).1 := by
  intro hEq
  have hTargets := congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq
  change profile.third.1.1.1 = star.edge profile.doubleLabel at hTargets
  exact profile.labels_ne (star.edge_injective (hTargets.symm.trans profile.third_target))

theorem branchEdges_card : (branchEdges input profile hCard).card = 3 := by
  classical
  have hOldNe : (firstSplitPattern input profile hCard).candidate.oldSourceEdge profile.third.1 ≠
      (firstSplitPattern input profile hCard).candidate.oldSourceEdge (branchDouble profile hCard).1 :=
    fun h ↦ third_ne_double profile hCard (ResolutionCut.oldSourceEdge_injective _ h)
  simp [branchEdges, (old_ne_new input profile hCard profile.third.1 profile.third.1.1.2).symm,
    (old_ne_new input profile hCard (branchDouble profile hCard).1 profile.third.1.1.2).symm, hOldNe]

theorem branchEdges_subset : branchEdges input profile hCard ⊆
    nonDanglingIncident (firstSplitPattern input profile hCard).candidate.datum
      (branchVertex input profile hCard) := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  have hRel := sheet_rel_of_incident_block profile.third
  have hNewIncident : Incident candidate.datum (candidate.newSourceEdge profile.third.1.1.2)
      (branchVertex input profile hCard) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
      (ResolutionM11.LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) _))
  have hThirdIncident : Incident candidate.datum (candidate.oldSourceEdge profile.third.1)
      (branchVertex input profile hCard) := by
    have h := oldSourceEdge_incident_fresh candidate profile.third.1.1.1
      ((incident_wallBlock_sourceVertex_iff data block profile.third.1).mp profile.third.2).1 rfl
      profile.third.1.1.2
    simpa only [GluingDatum.sourceEdge_self] using h
  have hDoubleIncident : Incident candidate.datum (candidate.oldSourceEdge (branchDouble profile hCard).1)
      (branchVertex input profile hCard) :=
    oldSourceEdge_incident_fresh candidate _ (star.edge_mem_incidentEdges profile.doubleLabel) rfl _
  intro edge hEdge
  simp only [branchEdges, Finset.mem_insert, Finset.mem_singleton] at hEdge
  rcases hEdge with rfl | rfl | rfl
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨firstSplit_new_survives input profile hCard _ hRel, hNewIncident⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 _ profile.third_survives,
        hThirdIncident⟩
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 _ (branchDouble profile hCard).2,
        hDoubleIncident⟩

/-- Exact surviving occurrences at the distinguished new branch vertex. -/
theorem nonDanglingIncident_branchVertex :
    nonDanglingIncident (firstSplitPattern input profile hCard).candidate.datum
        (branchVertex input profile hCard) = branchEdges input profile hCard := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le (branchEdges_subset input profile hCard)
  rw [branchEdges_card, card_nonDanglingIncident]
  exact (NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge _ _).trans
    (firstSplit_right_card input profile hCard _ (sheet_rel_of_incident_block profile.third)).le

theorem nonDanglingValency_branchVertex :
    nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      (branchVertex input profile hCard) = 3 := by
  rw [← card_nonDanglingIncident, nonDanglingIncident_branchVertex, branchEdges_card]

include hCard in
/-- There are exactly the two literal sheets carried by the surviving third
occurrence and the deleted occurrence. -/
theorem selected_sheet_pair : (data.vertexPartition wall).block block.1 =
    {profile.third.1.1.2, profile.deleted.edge.1.1.2} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro sheet hSheet
    rcases Finset.mem_insert.mp hSheet with rfl | hSheet
    · exact (SheetPartition.mem_block_iff _ _ _).mpr (sheet_rel_of_incident_block profile.third)
    · rw [Finset.mem_singleton] at hSheet
      exact hSheet ▸ (SheetPartition.mem_block_iff _ _ _).mpr
        (sheet_rel_of_incident_block profile.deleted.edge)
  · rw [Finset.card_pair (third_sheet_ne_deleted profile hCard)]
    exact le_of_eq hCard

theorem deleted_fresh_valency_le_two :
    nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
        (freshVertex target) profile.deleted.edge.1.1.2) ≤ 2 := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) profile.deleted.edge.1.1.2
  change nonDanglingValency candidate.datum vertex ≤ 2
  have hIncident : Incident candidate.datum (candidate.oldSourceEdge profile.deleted.edge.1) vertex := by
    have h := oldSourceEdge_incident_fresh candidate profile.deleted.edge.1.1.1
      ((incident_wallBlock_sourceVertex_iff data block profile.deleted.edge.1).mp profile.deleted.edge.2).1
      rfl profile.deleted.edge.1.1.2
    simpa only [GluingDatum.sourceEdge_self] using h
  have hDangling := (ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
    (M11SourceGenus.firstSplit_sourceGenus input profile hCard) profile.deleted.edge.1).mpr
    profile.deleted.dangling
  have hPositive : 0 < ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
      fun edge ↦ IsDangling candidate.datum edge.1).card :=
    Finset.card_pos.mpr ⟨⟨candidate.oldSourceEdge profile.deleted.edge.1, hIncident⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDangling⟩⟩
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    firstSplit_right_card input profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge)] at hTotal
  omega

/-- Among every fresh-endpoint fibre, the unique branch is the actual third
survivor's sheet; background blocks introduce no branch vertex. -/
theorem fresh_branch_iff (sheet : Fin degree) :
    3 ≤ nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) ↔
      sheet = profile.third.1.1.2 := by
  constructor
  · intro hBranch
    by_cases hSelected : (data.vertexPartition wall).Rel block.1 sheet
    · have hSheet := (SheetPartition.mem_block_iff _ _ _).mpr hSelected
      rw [selected_sheet_pair profile hCard, Finset.mem_insert, Finset.mem_singleton] at hSheet
      rcases hSheet with hThird | rfl
      · exact hThird
      · have hLe := deleted_fresh_valency_le_two input profile hCard
        omega
    · rw [M11SplitStableLift.nonDanglingValency_background input profile hCard sheet hSelected] at hBranch
      have hLe := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data
        (data.sourceEndpoint wall sheet)
      rw [M11JoinedDescentGeometry.background_old_card_incident input profile sheet hSelected] at hLe
      omega
  · rintro rfl
    exact (nonDanglingValency_branchVertex input profile hCard).ge

/-- Every vertex over the left target leaf has surviving valency at most two. -/
theorem left_valency_le_two (sheet : Fin degree) :
    nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2 := by
  apply (NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge _ _).trans
  rw [firstSplit_left_card input profile hCard]
  split_ifs with hSelected
  · have hEqual := congrArg Finset.card ((data.vertexPartition wall).block_eq_of_rel hSelected)
    change (data.vertexPartition wall).blockCard block.1 =
      (data.vertexPartition wall).blockCard sheet at hEqual
    omega
  · omega

end DraismaVargas.LocalCases.M11SplitBranch
