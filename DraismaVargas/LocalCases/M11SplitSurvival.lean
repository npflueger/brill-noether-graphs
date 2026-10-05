module

public import DraismaVargas.LocalCases.M11SplitRows
public import DraismaVargas.LocalCases.M11SourceGenus
public import DraismaVargas.LocalCases.ResolutionPruning

@[expose] public section

/-!
# Survival of the distinguished new M11 split arms

At the right endpoint carried by the unique old dangling occurrence, one
retained edge survives, one remains dangling, and the new edge is the third
actual incidence. Non-dangling valency cannot be one, so the new edge survives.
The common degree-two left endpoint then transfers survival to the other arm.
This is the literal source-graph argument behind Figure 32, Base I.
-/

namespace DraismaVargas.LocalCases.M11SplitSurvival

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates M11SplitLeaves M11SplitRows
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- A trivalent source vertex with a survivor and a deleted occurrence must
have its other occurrence survive: non-dangling valency one is impossible. -/
theorem survives_of_trivalent_of_deleted (data : GluingDatum target degree)
    (hConnected : data.Connected) (vertex : data.SourceVertex)
    (survivor deleted other : IncidentSourceEdge data vertex)
    (hSurvivor : ¬ IsDangling data survivor.1) (hDeleted : IsDangling data deleted.1)
    (hDistinct : deleted ≠ other) (hCard : Fintype.card (IncidentSourceEdge data vertex) = 3) :
    ¬ IsDangling data other.1 := by
  classical
  intro hOther
  have hPair : ({deleted, other} : Finset (IncidentSourceEdge data vertex)) ⊆
      Finset.univ.filter (fun edge ↦ IsDangling data edge.1) := by
    intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDeleted⟩
    · rw [Finset.mem_singleton] at hEdge
      subst edge
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOther⟩
  have hTwo : 2 ≤ ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
      fun edge ↦ IsDangling data edge.1).card := by
    simpa [hDistinct] using Finset.card_le_card hPair
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge data vertex))) (p := fun edge ↦ IsDangling data edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ, hCard] at hTotal
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurvivor survivor.2
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected vertex
  omega

/-- A singleton source block has one incident source occurrence in each
incident target direction, hence the same degree as its target vertex. -/
theorem card_incident_sourceEndpoint_of_blockCard_one (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree)
    (hOne : (data.vertexPartition vertex).blockCard sheet = 1) :
    Fintype.card (IncidentSourceEdge data (data.sourceEndpoint vertex sheet)) =
      (GluingDatum.incidentEdges vertex).card := by
  classical
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges vertex,
    (data.edgePartition edge).blockCountWithin (data.vertexPartition vertex)
      ((data.vertexPartition vertex).repr sheet)) = _
  have hRepr : (data.vertexPartition vertex).blockCard ((data.vertexPartition vertex).repr sheet) = 1 := by
    unfold SheetPartition.blockCard
    rw [(data.vertexPartition vertex).block_eq_of_rel ((data.vertexPartition vertex).rel_repr_left sheet)]
    exact hOne
  have hSingleton := (data.vertexPartition vertex).block_eq_singleton_of_blockCard_eq_one _ hRepr
  simp only [SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _ hSingleton,
    Finset.sum_const, smul_eq_mul, mul_one]

theorem firstSplit_right_blockCard (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ((firstSplitPattern input profile hCard).candidate.datum.vertexPartition
      (freshVertex target)).blockCard sheet = 1 := by
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum, GlobalResolution.datum_vertexPartition_fresh]
  rw [LocalResolution.paste_right_blockCard]
  change (LocalResolution.onBlock (data.vertexPartition wall) block.1
    (splitResolutionAt (data.vertexPartition wall) block.1) (backgroundResolution (data.vertexPartition wall))
    ((data.vertexPartition wall).repr sheet)).right.blockCard sheet = 1
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hRel.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact (data.vertexPartition wall).splitBlock_blockCard_of_rel block.1 sheet hRel

theorem firstSplit_right_card (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) = 3 :=
  (card_incident_sourceEndpoint_of_blockCard_one _ _ _ (firstSplit_right_blockCard input profile hCard sheet hRel)).trans
    (firstSplit_target_valencies input profile hCard).2

/-- A retained old target occurrence assigned to the fresh side carries its
same-sheet source occurrence to that literal fresh source endpoint. -/
theorem oldSourceEdge_incident_fresh (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hRight : candidate.right edge = true) (sheet : Fin degree) :
    Incident candidate.datum (candidate.oldSourceEdge (data.sourceEdge edge sheet))
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  have hAtUp : occurrenceEquiv target wall candidate.right (some edge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right) (freshVertex target) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt ⊢
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_freshVertex_iff target wall candidate.right edge).mpr ⟨hAt, hRight⟩
  have hIncident := incident_sourceEdge_sourceEndpoint candidate.datum (freshVertex target)
    (occurrenceEquiv target wall candidate.right (some edge)) hAtUp sheet
  have hEq : candidate.datum.sourceEdge (occurrenceEquiv target wall candidate.right (some edge)) sheet =
      candidate.oldSourceEdge (data.sourceEdge edge sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) edge sheet
  exact hEq ▸ hIncident

theorem sheet_rel_of_incident_block {block : WallBlock data wall}
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hBlock := ((incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2).2
  exact block.2.trans (congrArg Subtype.val hBlock).symm

theorem deleted_target_eq_single {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    profile.deleted.edge.1.1.1 = star.edge profile.singleLabel := by
  rcases profile.cases with ⟨hTarget, _, _⟩ | ⟨_, hPair, _⟩
  · exact hTarget
  · have hFirst := sourceEdgeIndex_pos data profile.first.1
    have hSecond := sourceEdgeIndex_pos data profile.second.1
    omega

/-- In M11, every sheet in the double direction belongs to one of its two
actual survivors; the unique deleted occurrence is in the other direction. -/
theorem double_sourceEdge_survives {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling data (data.sourceEdge (star.edge profile.doubleLabel) sheet) := by
  let edge := star.edge profile.doubleLabel
  have hAt := star.edge_mem_incidentEdges profile.doubleLabel
  have hRefines := refines_of_mem_incidentEdges data hAt
  have hRepresentative := hRefines.rel ((data.edgePartition edge).rel_repr_right sheet)
  have hIncident : Incident data (data.sourceEdge edge sheet) (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    exact ⟨hAt, Subtype.ext (hRepresentative.symm.trans (hRel.symm.trans block.2))⟩
  intro hDangling
  have hDeleted := (profile.deleted.unique ⟨data.sourceEdge edge sheet, hIncident⟩).mp hDangling
  have hTarget : star.edge profile.doubleLabel = profile.deleted.edge.1.1.1 :=
    congrArg (fun item : IncidentSourceEdge data (WallBlock.sourceVertex data wall block) ↦ item.1.1.1) hDeleted
  exact profile.labels_ne (star.edge_injective (hTarget.trans (deleted_target_eq_single profile hCard)))

/-- The new arm on the old deleted occurrence's sheet really survives.
This is the first nonempty new-fibre witness, not an assumed stable row. -/
theorem firstSplit_deleted_arm_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge profile.deleted.edge.1.1.2) := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let sheet := profile.deleted.edge.1.1.2
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  let oldSurvivor := data.sourceEdge (star.edge profile.doubleLabel) sheet
  have hRel : (data.vertexPartition wall).Rel block.1 sheet := sheet_rel_of_incident_block profile.deleted.edge
  have hSurvivorIncident : Incident candidate.datum (candidate.oldSourceEdge oldSurvivor) vertex :=
    oldSourceEdge_incident_fresh candidate _ (star.edge_mem_incidentEdges profile.doubleLabel) rfl sheet
  have hDeletedIncident : Incident candidate.datum (candidate.oldSourceEdge profile.deleted.edge.1) vertex := by
    have h := oldSourceEdge_incident_fresh candidate profile.deleted.edge.1.1.1
      ((incident_wallBlock_sourceVertex_iff data block profile.deleted.edge.1).mp profile.deleted.edge.2).1 rfl sheet
    simpa only [sheet, GluingDatum.sourceEdge_self] using h
  have hNewIncident : Incident candidate.datum (candidate.newSourceEdge sheet) vertex :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))
  have hDeleted := (ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
    (M11SourceGenus.firstSplit_sourceGenus input profile hCard) profile.deleted.edge.1).mpr profile.deleted.dangling
  have hSurvives := ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 oldSurvivor
    (double_sourceEdge_survives profile hCard sheet hRel)
  apply survives_of_trivalent_of_deleted candidate.datum (firstSplit_valid input profile hCard).1 vertex
    ⟨candidate.oldSourceEdge oldSurvivor, hSurvivorIncident⟩
    ⟨candidate.oldSourceEdge profile.deleted.edge.1, hDeletedIncident⟩
    ⟨candidate.newSourceEdge sheet, hNewIncident⟩ hSurvives hDeleted
  · intro hEqual
    have hTargets := congrArg (fun item : IncidentSourceEdge candidate.datum vertex ↦ item.1.1.1) hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTargets
    cases hLabels
  · exact firstSplit_right_card input profile hCard sheet hRel

/-- Every distinguished first-split arm survives, by propagation through
the actual common degree-two left endpoint. -/
theorem firstSplit_new_survives (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet) := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let chosen := profile.deleted.edge.1.1.2
  have hChosen := firstSplit_deleted_arm_survives input profile hCard
  by_cases hEqual : candidate.newSourceEdge sheet = candidate.newSourceEdge chosen
  · exact hEqual ▸ hChosen
  intro hDangling
  apply hChosen
  have hIncident (place : Fin degree) (hPlace : (data.vertexPartition wall).Rel block.1 place) :
      Incident candidate.datum (candidate.newSourceEdge place)
        (candidate.datum.sourceEndpoint (oldVertex target wall) block.1) :=
    Or.inl ((newSourceEdge_fst candidate place).trans
      (left_endpoint_eq_of_split candidate block.1 place (fun _ ↦ rfl) hPlace))
  apply isDangling_of_incident_of_vertex_degree_eq_two candidate.datum hEqual (hIncident sheet hRel)
    (hIncident chosen (sheet_rel_of_incident_block profile.deleted.edge)) _ hDangling
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge]
  have hTwo := firstSplit_left_card input profile hCard block.1
  rw [ite_eq_left (show (data.vertexPartition wall).Rel block.1 block.1 from rfl), hCard] at hTwo
  exact_mod_cast hTwo

/-- The exact new-fibre survival criterion for the first split. -/
theorem firstSplit_new_survives_iff (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet)) ↔
      (data.vertexPartition wall).Rel block.1 sheet := by
  constructor
  · intro hSurvives
    by_contra hBackground
    exact hSurvives (firstSplit_background_isDangling input profile hCard sheet hBackground)
  · exact firstSplit_new_survives input profile hCard sheet

/-- At a trivalent source vertex with a dangling occurrence, its two
surviving occurrences are consecutive and therefore share one stable class. -/
theorem stablePath_eq_of_trivalent_deleted (data : GluingDatum target degree)
    (hConnected : data.Connected) (first second : NonDanglingEdge data)
    (vertex : data.SourceVertex) (hFirst : Incident data first.1 vertex)
    (hSecond : Incident data second.1 vertex) (deleted : IncidentSourceEdge data vertex)
    (hDeleted : IsDangling data deleted.1) (hCard : Fintype.card (IncidentSourceEdge data vertex) = 3) :
    first.stablePath = second.stablePath := by
  classical
  by_cases hEqual : first = second
  · rw [hEqual]
  apply stablePath_eq_of_consecutive
  refine ⟨hEqual, vertex, hFirst, hSecond, ?_⟩
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data first.2 hFirst
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected vertex
  have hDeletedCount : 0 < ((Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
      fun edge ↦ IsDangling data edge.1).card :=
    Finset.card_pos.mpr ⟨deleted, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDeleted⟩⟩
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge data vertex))) (p := fun edge ↦ IsDangling data edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ, hCard] at hTotal
  omega

/-- The retained survivor in the double direction on the deleted occurrence's
sheet. This is the first split's `e1` row in Figure 32; it is not necessarily
`profile.first`, since that occurrence pair has an arbitrary enumeration. -/
noncomputable def firstSplit_retainedDouble (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum :=
  ⟨(firstSplitPattern input profile hCard).candidate.oldSourceEdge
      (data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2),
    ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
      (double_sourceEdge_survives profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge))⟩

theorem firstSplit_deleted_arm_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    NonDanglingEdge.stablePath
        ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge profile.deleted.edge.1.1.2,
          firstSplit_deleted_arm_survives input profile hCard⟩ =
      (firstSplit_retainedDouble input profile hCard).stablePath := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let sheet := profile.deleted.edge.1.1.2
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  have hDeletedIncident : Incident candidate.datum (candidate.oldSourceEdge profile.deleted.edge.1) vertex := by
    have h := oldSourceEdge_incident_fresh candidate profile.deleted.edge.1.1.1
      ((incident_wallBlock_sourceVertex_iff data block profile.deleted.edge.1).mp profile.deleted.edge.2).1 rfl sheet
    simpa only [sheet, GluingDatum.sourceEdge_self] using h
  refine stablePath_eq_of_trivalent_deleted candidate.datum (firstSplit_valid input profile hCard).1
    _ _ vertex ?_ ?_ ⟨candidate.oldSourceEdge profile.deleted.edge.1, hDeletedIncident⟩ ?_ ?_
  · exact Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))
  · exact oldSourceEdge_incident_fresh candidate _ (star.edge_mem_incidentEdges profile.doubleLabel) rfl sheet
  · exact (ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) profile.deleted.edge.1).mpr profile.deleted.dangling
  · exact firstSplit_right_card input profile hCard sheet (sheet_rel_of_incident_block profile.deleted.edge)

/-- Every distinguished new occurrence belongs to the actual retained `e1`
stable row; both its survival and the row identification are proved. -/
theorem firstSplit_new_stablePath_eq_retained (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    NonDanglingEdge.stablePath
        ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge sheet,
          firstSplit_new_survives input profile hCard sheet hRel⟩ =
      (firstSplit_retainedDouble input profile hCard).stablePath :=
  (firstSplit_new_stablePath_eq input profile hCard sheet profile.deleted.edge.1.1.2
    (firstSplit_new_survives input profile hCard sheet hRel)
    (firstSplit_deleted_arm_survives input profile hCard)).trans
    (firstSplit_deleted_arm_stablePath_eq input profile hCard)

end DraismaVargas.LocalCases.M11SplitSurvival
