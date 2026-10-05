module

public import DraismaVargas.LocalCases.W2M1kLeafStableLift

@[expose] public section

/-!
# Descending Figure 33's leaf member to incoming stable rows

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-1k}` and its Figure 33.

`M⁽¹⁾` has no `LimitChainCore.SelectedData`
(`W2M1kStableLift.leaf_not_wallCandidate`), so the core's `rowOfEdge` is
unavailable and the reverse map is built here directly, on the pattern of
`M11SplitRowDescent`: a retained occurrence goes back to its unique incoming
preimage, and **every** surviving regrown occurrence goes back to `e₁`
(`leafNewOldEdge`), because Base I.a prunes all but the retained pair's two
arms and those two share `e₁`'s row
(`W2M1kLeafStableLift.leaf_new_stablePath_eq_first`).

The induced-labelling rule of Part I (the edge labellings a limit inherits,
Section 5) is checked at each possible consecutive junction of the outgoing
member:

| junction | reader |
|---|---|
| target leaf, any sheet | `leafRowOfEdge_incident_left` |
| fresh endpoint over `{x}` (`nd = 2`) | `leafRowOfEdge_incident_fresh_pin` |
| fresh endpoint over `A₀ ∖ {x}` (`nd = 3`) | excluded by `leaf_nonDanglingValency_fresh_branch` |
| fresh endpoint off `A₀` | `leafRowOfEdge_incident_background` |
| unchanged off-wall vertex | `leafRowOfEdge_eq_away` |

Composing with `W2M1kLeafStableLift`'s lift gives an explicit geometric left
inverse, so the lift is injective; with its proved surjectivity this is the
geometric stable-row bijection `leafStablePathEquiv`.  No row count and no
supplied row correspondence enters.
-/

namespace DraismaVargas.LocalCases.W2M1kLeafRowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open W2M1kLeafStableLift
open LimitChainCore (pasted newSourceEdge_incident_old newSourceEdge_incident_fresh
  oldSourceEdge_ne_newSourceEdge)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The reverse map -/

/-- **The incoming occurrence every surviving regrown occurrence of `M⁽¹⁾`
represents**: `e₁`, for both arms of the retained pair. -/
noncomputable def leafNewOldEdge (profile : W2R2SourceProfile.SourceProfile data star block) :
    NonDanglingEdge data :=
  ⟨profile.first.1, profile.first_survives⟩

/-- Retained occurrences return to their unique incoming preimage; regrown
occurrences return to `e₁`'s row. -/
noncomputable def leafRowOfEdge (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge (LeafPair.candidate input shape pair) input.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else (leafNewOldEdge profile).stablePath

theorem leafRowOfEdge_retained (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (old : NonDanglingEdge data) :
    leafRowOfEdge input shape pair
        (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 old) =
      old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge (LeafPair.candidate input shape pair) input.valid.1 other =
        retainedEdge (LeafPair.candidate input shape pair) input.valid.1 old := ⟨old, rfl⟩
  rw [leafRowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective _ input.valid.1 (Classical.choose_spec hOld))

theorem leafRowOfEdge_new (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet)) :
    leafRowOfEdge input shape pair
        ⟨(LeafPair.candidate input shape pair).newSourceEdge sheet, hSurvives⟩ =
      (leafNewOldEdge profile).stablePath := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge (LeafPair.candidate input shape pair) input.valid.1 old =
        ⟨(LeafPair.candidate input shape pair).newSourceEdge sheet, hSurvives⟩ := by
    rintro ⟨old, hEqual⟩
    have hLabels := (occurrenceEquiv target wall
      (LeafPair.candidate input shape pair).right).injective
      (congrArg (fun occurrence :
        NonDanglingEdge (LeafPair.candidate input shape pair).datum ↦ occurrence.1.1.1) hEqual)
    cases hLabels
  exact dite_eq_right hNot

/-! ## §2  The junctions of the outgoing stable quotient -/

/-- **Only regrown occurrences meet the target leaf.**  The expanded retained
endpoint carries the new occurrence and nothing else
(`W2M1kSourceCandidates.leaf_target_valencies`). -/
theorem leafRowOfEdge_incident_left (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum)
    (hIncident : Incident (LeafPair.candidate input shape pair).datum edge.1
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet)) :
    leafRowOfEdge input shape pair edge = (leafNewOldEdge profile).stablePath := by
  rcases nonDanglingEdge_cases (LeafPair.candidate input shape pair) input.valid
      (leaf_sourceGenus input shape pair) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · have hTarget := (incident_iff_target_mem_and_rel _ _ _).mp hIncident |>.1
    change occurrenceEquiv target wall (LeafPair.candidate input shape pair).right
      (some old.1.1.1) ∈ GluingDatum.incidentEdges
        (target := graph target wall (LeafPair.candidate input shape pair).right)
        (oldVertex target wall) at hTarget
    rw [M11SplitLeaves.left_target_incident (LeafPair.candidate input shape pair)
      (leaf_target_valencies input shape pair).1, Finset.mem_singleton] at hTarget
    have hLabels := (occurrenceEquiv target wall
      (LeafPair.candidate input shape pair).right).injective hTarget
    cases hLabels
  · exact leafRowOfEdge_new input shape pair other hSurvives

/-- **At the trivalent endpoint over `{x}` every assigned row is `e₁`'s.**  Its
surviving star is the retained `e₁` together with the regrown occurrence through
`x` (`W2M1kStableGraph.leaf_nonDanglingIncident_fresh_pin`); `e₄` is pruned. -/
theorem leafRowOfEdge_incident_fresh_pin (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum)
    (hIncident : Incident (LeafPair.candidate input shape pair).datum edge.1
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0))) :
    leafRowOfEdge input shape pair edge = (leafNewOldEdge profile).stablePath := by
  classical
  have hMem : edge.1 ∈ nonDanglingIncident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) (pinSheet profile 0)) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
  rw [leaf_nonDanglingIncident_fresh_pin input shape pair, Finset.mem_insert,
    Finset.mem_singleton] at hMem
  rcases hMem with hEdge | hEdge
  · have hEq : edge = retainedEdge (LeafPair.candidate input shape pair) input.valid.1
        (leafNewOldEdge profile) := Subtype.ext hEdge
    rw [hEq]
    exact leafRowOfEdge_retained input shape pair (leafNewOldEdge profile)
  · have hEq : edge = ⟨(LeafPair.candidate input shape pair).newSourceEdge (pinSheet profile 0),
        leaf_new_pin_survives input shape pair⟩ := Subtype.ext hEdge
    rw [hEq]
    exact leafRowOfEdge_new input shape pair (pinSheet profile 0)
      (leaf_new_pin_survives input shape pair)

/-- **Background fresh vertices have only retained surviving incidences.** -/
theorem leafRowOfEdge_incident_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum)
    (hIncident : Incident (LeafPair.candidate input shape pair).datum edge.1
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint (freshVertex target) sheet)) :
    ∃ old : NonDanglingEdge data, Incident data old.1 (data.sourceEndpoint wall sheet) ∧
      leafRowOfEdge input shape pair edge = old.stablePath := by
  rcases nonDanglingEdge_cases (LeafPair.candidate input shape pair) input.valid
      (leaf_sourceGenus input shape pair) edge with ⟨old, rfl⟩ | ⟨other, hSurvives, rfl⟩
  · exact ⟨old, (leaf_background_old_incident_iff input shape pair sheet hBackground old.1).mp
      hIncident, leafRowOfEdge_retained input shape pair old⟩
  · have hRel := leaf_background_new_incident_rel input shape pair sheet other hBackground
      hIncident
    exact absurd (leaf_new_background_dangling input shape pair other
      (fun hOther ↦ hBackground (hOther.trans hRel.symm))) hSurvives

/-- Two incoming survivors at a background wall vertex of surviving valency two
share a stable row. -/
theorem leaf_background_old_stablePath_eq (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hValency : nonDanglingValency (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) sheet) = 2)
    (first second : NonDanglingEdge data)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet)) :
    first.stablePath = second.stablePath := by
  by_cases hEqual : first = second
  · rw [hEqual]
  · exact stablePath_eq_of_consecutive ⟨hEqual, _, hFirst, hSecond,
      (leaf_nonDanglingValency_background input shape pair sheet hBackground).symm.trans hValency⟩

/-- Away from the wall nothing changed. -/
theorem leafRowOfEdge_eq_away (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (LeafPair.candidate input shape pair).datum)
    (hFirst : Incident (LeafPair.candidate input shape pair).datum first.1
      (retainedVertex (LeafPair.candidate input shape pair) vertex))
    (hSecond : Incident (LeafPair.candidate input shape pair).datum second.1
      (retainedVertex (LeafPair.candidate input shape pair) vertex))
    (hValency : nonDanglingValency (LeafPair.candidate input shape pair).datum
      (retainedVertex (LeafPair.candidate input shape pair) vertex) = 2) :
    leafRowOfEdge input shape pair first = leafRowOfEdge input shape pair second := by
  classical
  have hGenus := leaf_sourceGenus input shape pair
  rcases nonDanglingEdge_cases (LeafPair.candidate input shape pair) input.valid hGenus first with
    ⟨oldFirst, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · rcases nonDanglingEdge_cases (LeafPair.candidate input shape pair) input.valid hGenus
      second with ⟨oldSecond, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · rw [leafRowOfEdge_retained, leafRowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff _ vertex hAway oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff _ vertex hAway oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex _ input.valid hGenus vertex hAway).symm.trans
            hValency⟩
    · exact (not_incident_newSourceEdge _ vertex hAway sheet hSecond).elim
  · exact (not_incident_newSourceEdge _ vertex hAway sheet hFirst).elim

/-- **The reverse map is well defined on the outgoing stable quotient.** -/
theorem leafRowOfEdge_eq_of_consecutive (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (first second : NonDanglingEdge (LeafPair.candidate input shape pair).datum)
    (hConsecutive : Consecutive (LeafPair.candidate input shape pair).datum first second) :
    leafRowOfEdge input shape pair first = leafRowOfEdge input shape pair second := by
  classical
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : (LeafPair.candidate input shape pair).datum.sourceEndpoint
      vertex.1.1 vertex.1.2 = vertex :=
    ((LeafPair.candidate input shape pair).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : (LeafPair.candidate input shape pair).datum.sourceEndpoint
            (oldVertex target wall) vertex.1.2 = vertex :=
          (congrArg (fun place ↦ (LeafPair.candidate input shape pair).datum.sourceEndpoint
            place vertex.1.2) hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond
        exact (leafRowOfEdge_incident_left input shape pair vertex.1.2 first hFirst).trans
          (leafRowOfEdge_incident_left input shape pair vertex.1.2 second hSecond).symm
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          (LeafPair.candidate input shape pair) vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact leafRowOfEdge_eq_away input shape pair old (hOld ▸ hAt) first second hFirst
          hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : (LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) vertex.1.2 = vertex :=
        (congrArg (fun place ↦ (LeafPair.candidate input shape pair).datum.sourceEndpoint
          place vertex.1.2) hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      by_cases hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2
      · by_cases hPin : vertex.1.2 = pinSheet profile 0
        · rw [hPin] at hFirst hSecond
          exact (leafRowOfEdge_incident_fresh_pin input shape pair first hFirst).trans
            (leafRowOfEdge_incident_fresh_pin input shape pair second hSecond).symm
        · rw [leaf_nonDanglingValency_fresh_branch input shape pair vertex.1.2 hWall hPin]
            at hValency
          exact absurd hValency (by decide)
      · obtain ⟨oldFirst, hOldFirst, hFirstRow⟩ :=
          leafRowOfEdge_incident_background input shape pair vertex.1.2 hWall first hFirst
        obtain ⟨oldSecond, hOldSecond, hSecondRow⟩ :=
          leafRowOfEdge_incident_background input shape pair vertex.1.2 hWall second hSecond
        exact hFirstRow.trans ((leaf_background_old_stablePath_eq input shape pair vertex.1.2
          hWall hValency oldFirst oldSecond hOldFirst hOldSecond).trans hSecondRow.symm)

/-! ## §3  The stable-row bijection -/

/-- The reverse geometric map on `M⁽¹⁾`'s stable-row quotient. -/
noncomputable def leafStablePathDescend (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    StablePath (LeafPair.candidate input shape pair).datum → StablePath data :=
  Quot.lift (leafRowOfEdge input shape pair) (leafRowOfEdge_eq_of_consecutive input shape pair)

@[simp] theorem leafStablePathDescend_mk (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum) :
    leafStablePathDescend input shape pair edge.stablePath =
      leafRowOfEdge input shape pair edge := rfl

theorem leafStablePathDescend_lift (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (path : StablePath data) :
    leafStablePathDescend input shape pair (leafStablePathLift input shape pair path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact leafRowOfEdge_retained input shape pair edge

theorem leafStablePathLift_injective (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Function.Injective (leafStablePathLift input shape pair) :=
  Function.LeftInverse.injective (leafStablePathDescend_lift input shape pair)

/-- **`M⁽¹⁾`'s geometric stable-row bijection.**  The forward map is literally
the retained-occurrence lift. -/
noncomputable def leafStablePathEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    StablePath data ≃ StablePath (LeafPair.candidate input shape pair).datum :=
  Equiv.ofBijective (leafStablePathLift input shape pair)
    ⟨leafStablePathLift_injective input shape pair,
      leafStablePathLift_surjective input shape pair⟩

@[simp] theorem leafStablePathEquiv_mk (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : NonDanglingEdge data) :
    leafStablePathEquiv input shape pair edge.stablePath =
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 edge).stablePath := rfl

@[simp] theorem leafStablePathEquiv_symm (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (path : StablePath (LeafPair.candidate input shape pair).datum) :
    (leafStablePathEquiv input shape pair).symm path =
      leafStablePathDescend input shape pair path := by
  obtain ⟨row, hRow⟩ := leafStablePathLift_surjective input shape pair path
  rw [← hRow, leafStablePathDescend_lift]
  exact (leafStablePathEquiv input shape pair).symm_apply_apply row

end DraismaVargas.LocalCases.W2M1kLeafRowDescent
