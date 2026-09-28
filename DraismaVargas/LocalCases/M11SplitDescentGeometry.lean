import DraismaVargas.LocalCases.M11SplitStableLift
import DraismaVargas.LocalCases.M11SplitColumn
import DraismaVargas.LocalCases.M11JoinedDescentGeometry

/-!
# Reverse local row checks for the first M11 split

Figure 32 of Draisma--Vargas Part I and its induced-labelling rule send
retained occurrences back to their old rows. At the singleton fresh vertices
the actual three-versus-two incidence census forces any divalent surviving
vertex onto the unique old deleted occurrence's sheet. Its retained survivor is
the double-direction occurrence on that sheet, not an arbitrarily enumerated
first occurrence.
-/

namespace DraismaVargas.LocalCases.M11SplitDescentGeometry

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableLocalProperties
open M11SourceCandidates M11SplitSurvival M11SplitColumn

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The selected fresh vertices are singletons: literal incident occurrence
representatives, not just their old wall blocks, determine the vertex. -/
theorem fresh_incident_sheet (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel block.1 sheet)
    (edge : (firstSplitPattern input profile hCard).candidate.datum.SourceEdge)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum edge
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    edge.1.2 = sheet := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  let partition := candidate.datum.vertexPartition (freshVertex target)
  have hRel := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.2
  change partition.Rel (partition.repr sheet) edge.1.2 at hRel
  have hRel' : partition.Rel sheet edge.1.2 := by
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel
  have hMem := (partition.mem_block_iff sheet edge.1.2).mpr hRel'
  rw [partition.block_eq_singleton_of_blockCard_eq_one sheet
    (firstSplit_right_blockCard input profile hCard sheet hSelected), Finset.mem_singleton] at hMem
  exact hMem

/-- The old occurrence incident to a selected fresh vertex is incident to
the original distinguished wall block and has that same literal sheet. -/
theorem retained_incident_fresh_data (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel block.1 sheet)
    (edge : data.SourceEdge)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.oldSourceEdge edge)
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    Incident data edge (WallBlock.sourceVertex data wall block) ∧ edge.1.2 = sheet := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  have hSheet : edge.1.2 = sheet := fresh_incident_sheet input profile hCard sheet hSelected _ hIncident
  have hTarget := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.1
  change occurrenceEquiv target wall candidate.right (some edge.1.1) ∈
    GluingDatum.incidentEdges (freshVertex target) at hTarget
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hTarget
  rw [occurrenceEquiv_some] at hTarget
  have hAt := (oldEnds_incident_freshVertex_iff target wall candidate.right edge.1.1).mp hTarget |>.1
  refine ⟨(incident_iff_target_mem_and_rel _ _ _).mpr ⟨?_, ?_⟩, hSheet⟩
  · change edge.1.1 ∈ GluingDatum.incidentEdges wall
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hAt
  · change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr block.1) edge.1.2
    rw [hSheet]
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hSelected

/-- A selected fresh vertex can be divalent after pruning only on the
unique deleted occurrence's sheet. The other sheet retains three survivors.
We find the deleted incidence from the actual three-versus-two census. -/
theorem fresh_valency_two_sheet_eq_deleted (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel block.1 sheet)
    (hValency : nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2) :
    sheet = profile.deleted.edge.1.1.2 := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  let vertex := candidate.datum.sourceEndpoint (freshVertex target) sheet
  have hTotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)))
    (p := fun edge ↦ IsDangling candidate.datum edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
    firstSplit_right_card input profile hCard sheet hSelected, hValency] at hTotal
  have hNonempty : ((Finset.univ : Finset (IncidentSourceEdge candidate.datum vertex)).filter
      fun edge ↦ IsDangling candidate.datum edge.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨edge, hEdge⟩ := hNonempty
  have hDangling := (Finset.mem_filter.mp hEdge).2
  rcases ResolutionPruning.sourceEdge_cases candidate edge.1 with ⟨old, hOld⟩ | ⟨newSheet, hNew⟩
  · have hIncident : Incident candidate.datum (candidate.oldSourceEdge old) vertex := hOld ▸ edge.2
    obtain ⟨hAt, hSheet⟩ := retained_incident_fresh_data input profile hCard sheet hSelected old hIncident
    have hOldDangling := (ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) old).mp (hOld ▸ hDangling)
    have hDeleted := (profile.deleted.unique ⟨old, hAt⟩).mp hOldDangling
    exact hSheet.symm.trans (congrArg (fun item ↦ item.1.1.2) hDeleted)
  · have hIncident : Incident candidate.datum (candidate.newSourceEdge newSheet) vertex := hNew ▸ edge.2
    have hSheet := fresh_incident_sheet input profile hCard sheet hSelected _ hIncident
    rw [firstSplit_newSourceEdge_sheet] at hSheet
    have hSurvives := firstSplit_new_survives input profile hCard newSheet (hSheet.symm ▸ hSelected)
    exact (hSurvives (hNew ▸ hDangling)).elim

/-- Every retained survivor at the selected divalent fresh vertex is the
double-direction occurrence on the deleted sheet, exactly Figure 32's e1. -/
theorem retained_survivor_eq_double (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel block.1 sheet)
    (hValency : nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (edge : NonDanglingEdge data)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.oldSourceEdge edge.1)
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    edge.1 = data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2 := by
  have hChosen := fresh_valency_two_sheet_eq_deleted input profile hCard sheet hSelected hValency
  obtain ⟨hAt, hSheet⟩ := retained_incident_fresh_data input profile hCard sheet hSelected edge.1 hIncident
  have hOldTarget := (incident_iff_target_mem_and_rel _ _ _).mp hAt |>.1
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge.1.1.1, hOldTarget⟩
  have hTarget : edge.1.1.1 = star.edge label := (congrArg Subtype.val hLabel).symm
  have hLabels := profile.labels_ne
  have hCases : label = profile.doubleLabel ∨ label = profile.singleLabel := by omega
  rcases hCases with hDouble | hSingle
  · rw [hDouble] at hTarget
    exact (GluingDatum.sourceEdge_self data edge.1).symm.trans
      (congrArg₂ data.sourceEdge hTarget (hSheet.trans hChosen))
  · have hEqual : edge.1 = profile.deleted.edge.1 := by
      apply Subtype.ext
      exact Prod.ext (hTarget.trans ((congrArg star.edge hSingle).trans
        (deleted_target_eq_single profile hCard).symm)) (hSheet.trans hChosen)
    exact (edge.2 (hEqual ▸ profile.deleted.dangling)).elim

end DraismaVargas.LocalCases.M11SplitDescentGeometry
