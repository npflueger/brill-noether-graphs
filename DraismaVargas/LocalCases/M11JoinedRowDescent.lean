import DraismaVargas.LocalCases.M11JoinedDescentGeometry

/-!
# Descending actual joined M11 occurrences to old stable rows

A retained occurrence goes back to itself. A new distinguished occurrence
goes to the original third occurrence, and a new background occurrence goes
to the original label-0 occurrence in its wall block. All survival proofs
are derived from the actual pruning equivalence. The local consecutive
checks, not an assumed row equivalence, make this a map on stable classes.
-/

namespace DraismaVargas.LocalCases.M11JoinedRowDescent

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11JoinedGeometry M11JoinedBackground M11JoinedSurvival
open ResolutionAwayFromWall M11JoinedStableLift M11JoinedDescentGeometry

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- A fixed original surviving occurrence representing a new joined edge. -/
noncomputable def newOldEdge (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet)) : NonDanglingEdge data := by
  classical
  exact if hRel : (data.vertexPartition wall).Rel block.1 sheet then
    ⟨profile.third.1, profile.third_survives⟩
  else ⟨data.sourceEdge (star.edge 0) sheet,
    fun h ↦ hSurvives ((background_isDangling_iff input profile hCard 0 sheet hRel).mpr h)⟩

theorem newOldEdge_of_selected (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet))
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    newOldEdge input profile hCard sheet hSurvives = ⟨profile.third.1, profile.third_survives⟩ := by
  exact dif_pos hRel

theorem newOldEdge_of_background (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet))
    (hRel : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (newOldEdge input profile hCard sheet hSurvives).1 = data.sourceEdge (star.edge 0) sheet := by
  have hEqual : newOldEdge input profile hCard sheet hSurvives =
      (⟨data.sourceEdge (star.edge 0) sheet,
        fun h ↦ hSurvives ((background_isDangling_iff input profile hCard 0 sheet hRel).mpr h)⟩ :
        NonDanglingEdge data) := dif_neg hRel
  exact congrArg Subtype.val hEqual

theorem newOldEdge_eq_of_rel (first second : Fin degree)
    (hFirst : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge first))
    (hSecond : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge second))
    (hRel : (data.vertexPartition wall).Rel first second) :
    newOldEdge input profile hCard first hFirst = newOldEdge input profile hCard second hSecond := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel block.1 first
  · rw [newOldEdge_of_selected input profile hCard first hFirst hSelected,
      newOldEdge_of_selected input profile hCard second hSecond (hSelected.trans hRel)]
  · have hOther : ¬ (data.vertexPartition wall).Rel block.1 second := fun h ↦ hSelected (h.trans hRel.symm)
    apply Subtype.ext
    rw [newOldEdge_of_background input profile hCard first hFirst hSelected,
      newOldEdge_of_background input profile hCard second hSecond hOther]
    apply background_sourceEdge_eq input profile 0 first hSelected
    · rfl
    · exact hRel.trans ((star.edgePartition_refines_wall data 0).rel
        ((data.edgePartition (star.edge 0)).rel_repr_right second))

theorem eq_newSourceEdge_of_not_retained
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hNot : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 old = edge) :
    edge.1 = (joinedPattern data star block hCard).candidate.newSourceEdge edge.1.1.2 := by
  let candidate := (joinedPattern data star block hCard).candidate
  rcases ResolutionPruning.sourceEdge_cases candidate edge.1 with ⟨old, hOld⟩ | ⟨sheet, hNew⟩
  · have hSurvives : ¬ IsDangling data old := by
      intro h
      apply edge.2
      rw [hOld]
      exact (ResolutionPruning.isDangling_oldSourceEdge_iff candidate input.valid
        (M11SourceGenus.joined_sourceGenus data star block hCard) old).mpr h
    exact (hNot ⟨⟨old, hSurvives⟩, Subtype.ext hOld.symm⟩).elim
  · exact M11SplitRows.eq_newSourceEdge_of_target candidate edge.1
      (congrArg (fun occurrence : candidate.datum.SourceEdge ↦ occurrence.1.1) hNew)

/-- Choose the unique retained preimage when there is one; otherwise the
occurrence is literally new and uses its fixed old representative. -/
noncomputable def rowOfEdge
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else (newOldEdge input profile hCard edge.1.1.2 (by
    rw [← eq_newSourceEdge_of_not_retained input hCard edge hOld]
    exact edge.2)).stablePath

theorem rowOfEdge_retained (old : NonDanglingEdge data) :
    rowOfEdge input profile hCard (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 old) =
      old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 other =
        retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge, dif_pos hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem rowOfEdge_new (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet)) :
    rowOfEdge input profile hCard ⟨(joinedPattern data star block hCard).candidate.newSourceEdge sheet, hSurvives⟩ =
      (newOldEdge input profile hCard sheet hSurvives).stablePath := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = ⟨candidate.newSourceEdge sheet, hSurvives⟩ := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1) hEqual)
    cases hLabels
  unfold rowOfEdge
  rw [dif_neg hNot]
  apply congrArg NonDanglingEdge.stablePath
  apply newOldEdge_eq_of_rel
  rw [newSourceEdge_sheet]
  exact (data.vertexPartition wall).rel_repr_left sheet

/-- At a background endpoint the assigned old row contains a genuine
occurrence incident to the original background vertex. -/
theorem rowOfEdge_incident_background (label : Fin 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hIncident : Incident (joinedPattern data star block hCard).candidate.datum edge.1
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet)) :
    ∃ old : NonDanglingEdge data, Incident data old.1 (data.sourceEndpoint wall sheet) ∧
      rowOfEdge input profile hCard edge = old.stablePath := by
  let candidate := (joinedPattern data star block hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid (M11SourceGenus.joined_sourceGenus data star block hCard) edge
      with ⟨old, rfl⟩ | ⟨newSheet, hSurvives, rfl⟩
  · have hData := retained_incident_endpoint_data block hCard label sheet old.1 hIncident
    refine ⟨old, ?_, rowOfEdge_retained input profile hCard old⟩
    apply (incident_iff_target_mem_and_rel _ _ _).mpr
    refine ⟨?_, ?_⟩
    · exact hData.1 ▸ star.edge_mem_incidentEdges label
    · exact ((data.vertexPartition wall).rel_repr_left sheet).trans hData.2
  · have hRel := new_incident_endpoint_rel block hCard label sheet newSheet hIncident
    have hBackground' : ¬ (data.vertexPartition wall).Rel block.1 newSheet :=
      fun h ↦ hBackground (h.trans hRel.symm)
    refine ⟨newOldEdge input profile hCard newSheet hSurvives, ?_, rowOfEdge_new input profile hCard newSheet hSurvives⟩
    rw [newOldEdge_of_background input profile hCard newSheet hSurvives hBackground']
    apply (incident_iff_target_mem_and_rel _ _ _).mpr
    refine ⟨star.edge_mem_incidentEdges 0, ?_⟩
    exact ((data.vertexPartition wall).rel_repr_left sheet).trans
      (hRel.trans ((star.edgePartition_refines_wall data 0).rel
        ((data.edgePartition (star.edge 0)).rel_repr_right newSheet)))

theorem rowOfEdge_incident_single
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hIncident : Incident (joinedPattern data star block hCard).candidate.datum edge.1
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
        (endpoint target wall profile.singleLabel) block.1)) :
    rowOfEdge input profile hCard edge =
      NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ := by
  let candidate := (joinedPattern data star block hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid (M11SourceGenus.joined_sourceGenus data star block hCard) edge
      with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · have hData := retained_incident_endpoint_data block hCard profile.singleLabel block.1 old.1 hIncident
    rw [rowOfEdge_retained]
    exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (single_retained_survivor_eq_third profile old hData.1 hData.2))
  · have hRel := new_incident_endpoint_rel block hCard profile.singleLabel block.1 sheet hIncident
    rw [rowOfEdge_new, newOldEdge_of_selected input profile hCard sheet hSurvives hRel]

theorem rowOfEdge_eq_at_endpoint (label : Fin 2) (sheet : Fin degree)
    (first second : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hFirst : Incident (joinedPattern data star block hCard).candidate.datum first.1
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet))
    (hSecond : Incident (joinedPattern data star block hCard).candidate.datum second.1
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet))
    (hValency : nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint (endpoint target wall label) sheet) = 2) :
    rowOfEdge input profile hCard first = rowOfEdge input profile hCard second := by
  classical
  by_cases hSelected : (data.vertexPartition wall).Rel block.1 sheet
  · have hEndpoint := endpoint_eq_of_rel data star block hCard label sheet block.1 hSelected.symm
    rw [hEndpoint] at hFirst hSecond hValency
    by_cases hDouble : label = profile.doubleLabel
    · rw [hDouble] at hValency
      exact (double_endpoint_valency_ne_two input profile hCard hValency).elim
    · have hSingle : label = profile.singleLabel := by
        have hLabels := profile.labels_ne
        omega
      rw [hSingle] at hFirst hSecond
      exact (rowOfEdge_incident_single input profile hCard first hFirst).trans
        (rowOfEdge_incident_single input profile hCard second hSecond).symm
  · obtain ⟨oldFirst, hOldFirst, hFirstRow⟩ := rowOfEdge_incident_background input profile hCard label sheet hSelected first hFirst
    obtain ⟨oldSecond, hOldSecond, hSecondRow⟩ := rowOfEdge_incident_background input profile hCard label sheet hSelected second hSecond
    exact hFirstRow.trans ((background_old_stablePath_eq input profile sheet hSelected oldFirst oldSecond hOldFirst hOldSecond).trans
      hSecondRow.symm)

theorem rowOfEdge_eq_away (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hFirst : Incident (joinedPattern data star block hCard).candidate.datum first.1
      (retainedVertex (joinedPattern data star block hCard).candidate vertex))
    (hSecond : Incident (joinedPattern data star block hCard).candidate.datum second.1
      (retainedVertex (joinedPattern data star block hCard).candidate vertex))
    (hValency : nonDanglingValency (joinedPattern data star block hCard).candidate.datum
      (retainedVertex (joinedPattern data star block hCard).candidate vertex) = 2) :
    rowOfEdge input profile hCard first = rowOfEdge input profile hCard second := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  have hGenus := M11SourceGenus.joined_sourceGenus data star block hCard
  rcases nonDanglingEdge_cases candidate input.valid hGenus first with ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases candidate input.valid hGenus second with ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [rowOfEdge_retained, rowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff candidate vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff candidate vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex candidate input.valid hGenus vertex hAway).symm.trans hValency⟩
    · exact (not_incident_newSourceEdge candidate vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge candidate vertex hAway sheet hFirst).elim

theorem rowOfEdge_eq_of_consecutive
    (first second : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum)
    (hConsecutive : Consecutive (joinedPattern data star block hCard).candidate.datum first second) :
    rowOfEdge input profile hCard first = rowOfEdge input profile hCard second := by
  classical
  let candidate := (joinedPattern data star block hCard).candidate
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : candidate.datum.sourceEndpoint (endpoint target wall 0) vertex.1.2 = vertex := by
          have hPlace : endpoint target wall 0 = vertex.1.1 := hTarget.symm
          exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2) hPlace).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        exact rowOfEdge_eq_at_endpoint input profile hCard 0 vertex.1.2 first second hFirst hSecond hValency
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact rowOfEdge_eq_away input profile hCard old (hOld ▸ hAt) first second hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : candidate.datum.sourceEndpoint (endpoint target wall 1) vertex.1.2 = vertex := by
        have hPlace : endpoint target wall 1 = vertex.1.1 := hTarget.symm
        exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2) hPlace).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      exact rowOfEdge_eq_at_endpoint input profile hCard 1 vertex.1.2 first second hFirst hSecond hValency

/-- The reverse geometric map on the actual joined stable-row quotient. -/
noncomputable def stablePathDescend :
    StablePath (joinedPattern data star block hCard).candidate.datum → StablePath data :=
  Quot.lift (rowOfEdge input profile hCard) (rowOfEdge_eq_of_consecutive input profile hCard)

@[simp] theorem stablePathDescend_mk
    (edge : NonDanglingEdge (joinedPattern data star block hCard).candidate.datum) :
    stablePathDescend input profile hCard edge.stablePath = rowOfEdge input profile hCard edge := rfl

theorem stablePathDescend_lift (path : StablePath data) :
    stablePathDescend input profile hCard (stablePathLift input profile hCard path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact rowOfEdge_retained input profile hCard edge

theorem stablePathLift_injective : Function.Injective (stablePathLift input profile hCard) :=
  Function.LeftInverse.injective (stablePathDescend_lift input profile hCard)

/-- The compatible geometric row dictionary, with the forward map literally
the retained-occurrence lift and no assumed cardinality or row equivalence. -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath (joinedPattern data star block hCard).candidate.datum :=
  Equiv.ofBijective (stablePathLift input profile hCard)
    ⟨stablePathLift_injective input profile hCard, stablePathLift_surjective input profile hCard⟩

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv input profile hCard edge.stablePath =
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge).stablePath := rfl

end DraismaVargas.LocalCases.M11JoinedRowDescent
