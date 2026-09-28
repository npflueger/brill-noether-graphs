import DraismaVargas.LocalCases.M11JoinedStableLift

/-!
# Local checks for descending joined M11 stable rows

At the distinguished double-direction endpoint all three incidences survive;
at the single-direction endpoint the only retained survivor is the third
occurrence. Background endpoints just subdivide the old divalent block.
These are the reverse local checks for the induced row labelling of Figure 32
of Draisma--Vargas Part I (Case `{w2-r2-nd3-M-11}`).
-/

namespace DraismaVargas.LocalCases.M11JoinedDescentGeometry

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11JoinedGeometry M11JoinedBackground M11JoinedSurvival

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance (block : WallBlock data wall)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    DecidableEq (graph target wall (joinedPattern data star block hCard).candidate.right).edges := by
  unfold Multiset.ToType
  infer_instance

theorem retained_incident_endpoint_data
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (label : Fin 2) (sheet : Fin degree) (edge : data.SourceEdge)
    (hIncident : Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.oldSourceEdge edge)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet)) :
    edge.1.1 = star.edge label ∧ (data.vertexPartition wall).Rel sheet edge.1.2 := by
  classical
  have h := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
  have hTarget := h.1
  change occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right (some edge.1.1) ∈
    GluingDatum.incidentEdges (endpoint target wall label) at hTarget
  rw [target_incident_pair] at hTarget
  rcases Finset.mem_insert.mp hTarget with hNew | hOld
  · have hLabels := (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right).injective hNew
    cases hLabels
  · have hLabels := (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right).injective
      (Finset.mem_singleton.mp hOld)
    refine ⟨Option.some.inj hLabels, ?_⟩
    have hRel := h.2
    change ((joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label)).Rel
      (((joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label)).repr sheet)
      edge.1.2 at hRel
    rw [vertexPartition_endpoint] at hRel
    simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel

theorem new_incident_endpoint_rel
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (label : Fin 2) (anchor sheet : Fin degree)
    (hIncident : Incident (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet)
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) anchor)) :
    (data.vertexPartition wall).Rel anchor sheet := by
  have hRel := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.2
  change ((joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label)).Rel
    (((joinedPattern data star block hCard).candidate.datum.vertexPartition (endpoint target wall label)).repr anchor)
    ((joinedPattern data star block hCard).candidate.newSourceEdge sheet).1.2 at hRel
  rw [vertexPartition_endpoint, newSourceEdge_sheet] at hRel
  simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel

theorem background_old_card_incident (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    Fintype.card (IncidentSourceEdge data (data.sourceEndpoint wall sheet)) = 2 := by
  have h := W2SourceInput.card_incidentSourceEdge_wallBlock (data := data) star
    ((data.vertexPartition wall).toBlock sheet)
  rw [background_ramification_zero input profile sheet hBackground] at h
  have hVertex : WallBlock.sourceVertex data wall ((data.vertexPartition wall).toBlock sheet) =
      data.sourceEndpoint wall sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (data.vertexPartition wall).repr_idem sheet
  rw [hVertex] at h
  omega

theorem background_old_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree) (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (first second : NonDanglingEdge data)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet)) :
    first.stablePath = second.stablePath :=
  M11SplitRows.stablePath_eq_of_incident_card_two data input.valid.1 first second _ hFirst hSecond
    (background_old_card_incident input profile sheet hBackground)

theorem single_retained_survivor_eq_third
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (edge : NonDanglingEdge data) (hTarget : edge.1.1.1 = star.edge profile.singleLabel)
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.1.2) : edge.1 = profile.third.1 := by
  classical
  have hIncident : Incident data edge.1 (WallBlock.sourceVertex data wall block) := by
    apply (incident_iff_target_mem_and_rel _ _ _).mpr
    refine ⟨?_, ?_⟩
    · exact hTarget ▸ star.edge_mem_incidentEdges profile.singleLabel
    · change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr block.1) edge.1.1.2
      simpa only [SheetPartition.Rel, SheetPartition.repr_idem] using hRel
  have hMember := (W2R2SourceProfile.survivingFibre.mem data star block profile.singleLabel ⟨edge.1, hIncident⟩).mpr
    ⟨hTarget, edge.2⟩
  rw [profile.single_fibre] at hMember
  have hEqual : (⟨edge.1, hIncident⟩ : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) =
      profile.third := Finset.mem_singleton.mp hMember
  exact congrArg Subtype.val hEqual

/-- The double-direction endpoint cannot be a stable-path joining vertex:
the two original double occurrences and the new occurrence all survive. -/
theorem double_endpoint_valency_ne_two (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall profile.doubleLabel) block.1) ≠ 2 := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  let vertex := candidate.datum.sourceEndpoint (endpoint target wall profile.doubleLabel) block.1
  let first := candidate.oldSourceEdge profile.first.1
  let second := candidate.oldSourceEdge profile.second.1
  let newEdge := candidate.newSourceEdge block.1
  have hFirst : first ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 _ profile.first_survives,
        oldSourceEdge_incident_of_target_rel data star block hCard _ _ profile.first_target _
          (M11SplitSurvival.sheet_rel_of_incident_block profile.first)⟩
  have hSecond : second ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge candidate input.valid.1 _ profile.second_survives,
        oldSourceEdge_incident_of_target_rel data star block hCard _ _ profile.second_target _
          (M11SplitSurvival.sheet_rel_of_incident_block profile.second)⟩
  have hNew : newEdge ∈ nonDanglingIncident candidate.datum vertex :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨joined_distinguished_survives input profile hCard,
        newSourceEdge_incident_endpoint data star block hCard _ _⟩
  have hFirstSecond : first ≠ second := fun h ↦ profile.first_ne_second
    (Subtype.ext (ResolutionCut.oldSourceEdge_injective candidate h))
  have hOldNew : ∀ old : data.SourceEdge, candidate.oldSourceEdge old ≠ newEdge := by
    intro old hEqual
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEqual)
    cases hLabels
  have hSubset : ({first, second, newEdge} : Finset candidate.datum.SourceEdge) ⊆
      nonDanglingIncident candidate.datum vertex := by
    intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact hFirst
    · exact hSecond
    · exact hNew
  have hThree : 3 ≤ nonDanglingValency candidate.datum vertex := by
    have hCount := Finset.card_le_card hSubset
    simpa [hFirstSecond, hOldNew, first, second, newEdge, ← card_nonDanglingIncident] using hCount
  intro hTwo
  change nonDanglingValency candidate.datum vertex = 2 at hTwo
  omega

end DraismaVargas.LocalCases.M11JoinedDescentGeometry
