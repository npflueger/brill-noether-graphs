import DraismaVargas.LocalCases.M11RemotePruning

/-!
# Survival and the natural retained row of the remote M11 split

Use the actual image of the deleted occurrence under the branch swap. At its
fresh endpoint, the retained double-direction occurrence survives, the deleted
occurrence stays dangling, and the new arm is the third incidence. Hence the
new arm survives and shares the retained occurrence's stable row. The common
degree-two left endpoint transfers this to the other distinguished sheet.

This identifies a natural row of the second candidate. Its identification
with the original `e2` in Figure 32 uses target-tree branch separation, proved
separately in `M11BranchSeparation` and consumed by `M11RemoteColumn`.
-/

namespace DraismaVargas.LocalCases.M11RemoteSurvival

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates M11SplitLeaves M11SplitRows
open M11SplitSurvival M11RemotePruning

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

theorem secondSplit_right_blockCard (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ((secondSplitPattern input profile hCard).candidate.datum.vertexPartition
      (freshVertex target)).blockCard sheet = 1 := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum, GlobalResolution.datum_vertexPartition_fresh]
  rw [LocalResolution.paste_right_blockCard]
  let partition := (swappedDatum profile hCard).vertexPartition wall
  change (LocalResolution.onBlock partition block.1
    (splitResolutionAt partition block.1) (backgroundResolution partition)
    (partition.repr sheet)).right.blockCard sheet = 1
  have hSelected : partition.Rel block.1 sheet :=
    (congrArg (fun part : SheetPartition degree ↦ part.Rel block.1 sheet)
      (swappedDatum_vertexPartition profile hCard)).mpr hRel
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hSelected.trans (partition.rel_repr_right sheet))]
  exact partition.splitBlock_blockCard_of_rel block.1 sheet hSelected

theorem secondSplit_right_card (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 3 :=
  (card_incident_sourceEndpoint_of_blockCard_one _ _ _ (secondSplit_right_blockCard input profile hCard sheet hRel)).trans
    (secondSplit_target_valencies input profile hCard).2

theorem secondSplit_deleted_incident (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Incident (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.oldSourceEdge (swappedDeleted profile hCard))
      ((secondSplitPattern input profile hCard).candidate.datum.sourceEndpoint
        (freshVertex target) (swappedDeleted profile hCard).1.2) := by
  have hAt : (swappedDeleted profile hCard).1.1 ∈ GluingDatum.incidentEdges wall := by
    rw [swappedDeleted_target]
    exact star.edge_mem_incidentEdges profile.singleLabel
  have h := oldSourceEdge_incident_fresh (secondSplitPattern input profile hCard).candidate
    (swappedDeleted profile hCard).1.1 hAt rfl (swappedDeleted profile hCard).1.2
  simpa only [GluingDatum.sourceEdge_self] using h

theorem secondSplit_deleted_dangling (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.oldSourceEdge (swappedDeleted profile hCard)) :=
  (ResolutionPruning.isDangling_oldSourceEdge_iff _
    (wallBranchSwap_preserves_valid data input.valid wall _ _ _ _ _)
    ((M11SourceGenus.secondSplit_sourceGenus input profile hCard).trans
      (M11SourceGenus.swappedDatum_sourceGenus profile hCard).symm) _).mpr
    (swappedDeleted_dangling input.valid.1 profile hCard)

/-- A literal nonempty new-fibre witness after the remote swap and split. -/
theorem secondSplit_deleted_arm_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    ¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge (swappedDeleted profile hCard).1.2) := by
  let candidate := (secondSplitPattern input profile hCard).candidate
  let sheet := (swappedDeleted profile hCard).1.2
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  let oldSurvivor := (swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel) sheet
  have hRel := swappedDeleted_sheet_rel profile hCard
  have hSurvivorIncident : Incident candidate.datum (candidate.oldSourceEdge oldSurvivor) vertex :=
    oldSourceEdge_incident_fresh candidate _ (star.edge_mem_incidentEdges profile.doubleLabel) rfl sheet
  have hNewIncident : Incident candidate.datum (candidate.newSourceEdge sheet) vertex :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge (swappedDatum profile hCard) wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))
  have hSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge candidate
    (wallBranchSwap_preserves_valid data input.valid wall _ _ _ _ _).1 oldSurvivor
    (swapped_double_sourceEdge_survives input.valid.1 profile hCard sheet hRel)
  apply survives_of_trivalent_of_deleted candidate.datum (secondSplit_valid input profile hCard).1 vertex
    ⟨candidate.oldSourceEdge oldSurvivor, hSurvivorIncident⟩
    ⟨candidate.oldSourceEdge (swappedDeleted profile hCard), secondSplit_deleted_incident input profile hCard⟩
    ⟨candidate.newSourceEdge sheet, hNewIncident⟩ hSurvives (secondSplit_deleted_dangling input profile hCard)
  · intro hEqual
    have hTargets := congrArg (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact secondSplit_right_card input profile hCard sheet hRel

/-- The two distinguished arms both survive in the actual remote candidate. -/
theorem secondSplit_new_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet) := by
  let candidate := (secondSplitPattern input profile hCard).candidate
  let chosen := (swappedDeleted profile hCard).1.2
  have hChosen := secondSplit_deleted_arm_survives input profile hCard
  by_cases hEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen
  · exact hEqual ▸ hChosen
  intro hDangling
  apply hChosen
  have hIncident (place : Fin degree) (hPlace : (data.vertexPartition wall).Rel block.1 place) :
      Incident candidate.datum (candidate.newSourceEdge place)
        (candidate.datum.sourceEndpoint (oldVertex target wall) block.1) := by
    have hSelected : ((swappedDatum profile hCard).vertexPartition wall).Rel block.1 place := by
      rw [swappedDatum_vertexPartition]
      exact hPlace
    exact Or.inl ((newSourceEdge_fst candidate place).trans
      (left_endpoint_eq_of_split candidate block.1 place (fun _ ↦ rfl) hSelected))
  apply isDangling_of_incident_of_vertex_degree_eq_two candidate.datum hEqual (hIncident sheet hRel)
    (hIncident chosen (swappedDeleted_sheet_rel profile hCard)) _ hDangling
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge]
  have hTwo := secondSplit_left_card input profile hCard block.1
  rw [if_pos (show (data.vertexPartition wall).Rel block.1 block.1 from rfl), hCard] at hTwo
  exact_mod_cast hTwo

/-- Exact survival criterion, including arbitrary-size background blocks. -/
theorem secondSplit_new_survives_iff (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet)) ↔
      (data.vertexPartition wall).Rel block.1 sheet := by
  constructor
  · intro hSurvives
    by_contra hBackground
    exact hSurvives (secondSplit_background_isDangling input profile hCard sheet hBackground)
  · exact secondSplit_new_survives input profile hCard sheet

/-- The actual retained double-direction occurrence on the swapped deleted
occurrence's sheet. No identification with an original profile label is made. -/
noncomputable def secondSplit_retainedDouble (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (secondSplitPattern input profile hCard).candidate.datum :=
  ⟨(secondSplitPattern input profile hCard).candidate.oldSourceEdge
      ((swappedDatum profile hCard).sourceEdge (star.edge profile.doubleLabel) (swappedDeleted profile hCard).1.2),
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (wallBranchSwap_preserves_valid data input.valid wall _ _ _ _ _).1 _
      (swapped_double_sourceEdge_survives input.valid.1 profile hCard _ (swappedDeleted_sheet_rel profile hCard))⟩

theorem secondSplit_deleted_arm_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge.stablePath
        ⟨(secondSplitPattern input profile hCard).candidate.newSourceEdge (swappedDeleted profile hCard).1.2,
          secondSplit_deleted_arm_survives input profile hCard⟩ =
      (secondSplit_retainedDouble input profile hCard).stablePath := by
  let candidate := (secondSplitPattern input profile hCard).candidate
  let sheet := (swappedDeleted profile hCard).1.2
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  refine stablePath_eq_of_trivalent_deleted candidate.datum (secondSplit_valid input profile hCard).1
    _ _ vertex ?_ ?_
    ⟨candidate.oldSourceEdge (swappedDeleted profile hCard), secondSplit_deleted_incident input profile hCard⟩
    (secondSplit_deleted_dangling input profile hCard) ?_
  · exact Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge (swappedDatum profile hCard) wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))
  · exact oldSourceEdge_incident_fresh candidate _ (star.edge_mem_incidentEdges profile.doubleLabel) rfl sheet
  · exact secondSplit_right_card input profile hCard sheet (swappedDeleted_sheet_rel profile hCard)

/-- Every distinguished new occurrence belongs to the geometrically
identified retained row of the actual second split. -/
theorem secondSplit_new_stablePath_eq_retained (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        ⟨(secondSplitPattern input profile hCard).candidate.newSourceEdge sheet,
          secondSplit_new_survives input profile hCard sheet hRel⟩ =
      (secondSplit_retainedDouble input profile hCard).stablePath :=
  (secondSplit_new_stablePath_eq input profile hCard sheet (swappedDeleted profile hCard).1.2
    (secondSplit_new_survives input profile hCard sheet hRel)
    (secondSplit_deleted_arm_survives input profile hCard)).trans
    (secondSplit_deleted_arm_stablePath_eq input profile hCard)

end DraismaVargas.LocalCases.M11RemoteSurvival
