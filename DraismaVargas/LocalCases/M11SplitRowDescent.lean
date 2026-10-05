module

public import DraismaVargas.LocalCases.M11SplitDescentGeometry

@[expose] public section

/-!
# The first M11 split's actual stable-row bijection

Retained occurrences return to their old rows; new survivors return to the
old double-direction row on the deleted occurrence's sheet. The
induced-labelling rule of Draisma--Vargas Part I (the edge labellings a limit
inherits, Section 5) is checked at each possible consecutive junction:
new-only leaf, singleton selected fresh vertex, background fresh vertex,
and unchanged off-wall vertex. The resulting quotient map is a left inverse
of the retained-occurrence lift, proving its injectivity without row counts.
-/

namespace DraismaVargas.LocalCases.M11SplitRowDescent

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitSurvival M11SplitStableLift M11SplitDescentGeometry
open ResolutionAwayFromWall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The actual original double occurrence on the deleted sheet represents
every new survivor in the first split. -/
noncomputable def newOldEdge : NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2,
    double_sourceEdge_survives profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge)⟩

/-- Retained occurrences return to their unique old preimage; new
occurrences return to Figure 32's actual deleted-sheet double row. -/
noncomputable def rowOfEdge
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else (newOldEdge profile hCard).stablePath

theorem rowOfEdge_retained (old : NonDanglingEdge data) :
    rowOfEdge input profile hCard (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 old) =
      old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 other =
        retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem rowOfEdge_new (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet)) :
    rowOfEdge input profile hCard ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge sheet, hSurvives⟩ =
      (newOldEdge profile hCard).stablePath := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge candidate input.valid.1 old = ⟨candidate.newSourceEdge sheet, hSurvives⟩ := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall candidate.right).injective
      (congrArg (fun occurrence : NonDanglingEdge candidate.datum ↦ occurrence.1.1.1) hEqual)
    cases hLabels
  exact dite_eq_right hNot

/-- Only new target occurrences meet the left leaf endpoint. -/
theorem rowOfEdge_incident_left (sheet : Fin degree)
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum edge.1
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    rowOfEdge input profile hCard edge = (newOldEdge profile hCard).stablePath := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hTarget := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.1
    change occurrenceEquiv target wall candidate.right (some old.1.1.1) ∈
      GluingDatum.incidentEdges (oldVertex target wall) at hTarget
    rw [M11SplitLeaves.left_target_incident candidate (firstSplit_target_valencies input profile hCard).1,
      Finset.mem_singleton] at hTarget
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
    cases hLabels
  · exact rowOfEdge_new input profile hCard other hSurvives

/-- At a selected divalent fresh vertex, every assigned row is the
deleted-sheet double row; at the other selected vertex valency is not two. -/
theorem rowOfEdge_incident_fresh_selected (sheet : Fin degree)
    (hSelected : (data.vertexPartition wall).Rel block.1 sheet)
    (hValency : nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum edge.1
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    rowOfEdge input profile hCard edge = (newOldEdge profile hCard).stablePath := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · rw [rowOfEdge_retained]
    exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (retained_survivor_eq_double input profile hCard sheet hSelected hValency old hIncident))
  · exact rowOfEdge_new input profile hCard other hSurvives

/-- Background fresh vertices have only retained surviving incidences. -/
theorem rowOfEdge_incident_background (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet)
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hIncident : Incident (firstSplitPattern input profile hCard).candidate.datum edge.1
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data, Incident data old.1 (data.sourceEndpoint wall sheet) ∧
      rowOfEdge input profile hCard edge = old.stablePath := by
  let candidate := (firstSplitPattern input profile hCard).candidate
  rcases nonDanglingEdge_cases candidate input.valid
      (M11SourceGenus.firstSplit_sourceGenus input profile hCard) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · exact ⟨old, (background_old_incident_iff input profile hCard sheet hBackground old.1).mp hIncident,
      rowOfEdge_retained input profile hCard old⟩
  · have hRel := background_new_incident_rel input profile hCard sheet other hBackground hIncident
    exact (hBackground (((firstSplit_new_survives_iff input profile hCard other).mp hSurvives).trans hRel.symm)).elim

theorem rowOfEdge_eq_away (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hFirst : Incident (firstSplitPattern input profile hCard).candidate.datum first.1
      (retainedVertex (firstSplitPattern input profile hCard).candidate vertex))
    (hSecond : Incident (firstSplitPattern input profile hCard).candidate.datum second.1
      (retainedVertex (firstSplitPattern input profile hCard).candidate vertex))
    (hValency : nonDanglingValency (firstSplitPattern input profile hCard).candidate.datum
      (retainedVertex (firstSplitPattern input profile hCard).candidate vertex) = 2) :
    rowOfEdge input profile hCard first = rowOfEdge input profile hCard second := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  have hGenus := M11SourceGenus.firstSplit_sourceGenus input profile hCard
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
    (first second : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hConsecutive : Consecutive (firstSplitPattern input profile hCard).candidate.datum first second) :
    rowOfEdge input profile hCard first = rowOfEdge input profile hCard second := by
  classical
  let candidate := (firstSplitPattern input profile hCard).candidate
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 = vertex :=
    (candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : candidate.datum.sourceEndpoint (oldVertex target wall) vertex.1.2 = vertex := by
          exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2) hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond
        exact (rowOfEdge_incident_left input profile hCard vertex.1.2 first hFirst).trans
          (rowOfEdge_incident_left input profile hCard vertex.1.2 second hSecond).symm
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact rowOfEdge_eq_away input profile hCard old (hOld ▸ hAt) first second hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2 = vertex := by
        exact (congrArg (fun place ↦ candidate.datum.sourceEndpoint place vertex.1.2) hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      by_cases hSelected : (data.vertexPartition wall).Rel block.1 vertex.1.2
      · exact (rowOfEdge_incident_fresh_selected input profile hCard _ hSelected hValency first hFirst).trans
          (rowOfEdge_incident_fresh_selected input profile hCard _ hSelected hValency second hSecond).symm
      · obtain ⟨oldFirst, hOldFirst, hFirstRow⟩ :=
          rowOfEdge_incident_background input profile hCard _ hSelected first hFirst
        obtain ⟨oldSecond, hOldSecond, hSecondRow⟩ :=
          rowOfEdge_incident_background input profile hCard _ hSelected second hSecond
        exact hFirstRow.trans ((M11JoinedDescentGeometry.background_old_stablePath_eq input profile
          _ hSelected oldFirst oldSecond hOldFirst hOldSecond).trans hSecondRow.symm)

/-- The reverse map is proved well-defined on the actual stable quotient. -/
noncomputable def stablePathDescend :
    StablePath (firstSplitPattern input profile hCard).candidate.datum → StablePath data :=
  Quot.lift (rowOfEdge input profile hCard) (rowOfEdge_eq_of_consecutive input profile hCard)

@[simp] theorem stablePathDescend_mk
    (edge : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum) :
    stablePathDescend input profile hCard edge.stablePath = rowOfEdge input profile hCard edge := rfl

theorem stablePathDescend_lift (path : StablePath data) :
    stablePathDescend input profile hCard (stablePathLift input profile hCard path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact rowOfEdge_retained input profile hCard edge

theorem stablePathLift_injective : Function.Injective (stablePathLift input profile hCard) :=
  Function.LeftInverse.injective (stablePathDescend_lift input profile hCard)

/-- The first split's row bijection is the induced retained-occurrence map. -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath (firstSplitPattern input profile hCard).candidate.datum :=
  Equiv.ofBijective (stablePathLift input profile hCard)
    ⟨stablePathLift_injective input profile hCard, stablePathLift_surjective input profile hCard⟩

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv input profile hCard edge.stablePath =
      (retainedEdge (firstSplitPattern input profile hCard).candidate input.valid.1 edge).stablePath := rfl

end DraismaVargas.LocalCases.M11SplitRowDescent
