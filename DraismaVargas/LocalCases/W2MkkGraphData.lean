import DraismaVargas.LocalCases.W2MkkRowDescent

/-!
# Figure 34's stable incidence graph

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-kk} (abbreviated M-kk),
Figure 34.

`W2MkkStableLift` reads each Figure 34 member as the core's
`LimitChainCore.SelectedData` and `W2MkkRowDescent` turns that into the
member's geometric stable-row bijection.  What the certified exit also needs
is the **branch half**: a flag dictionary at the member's own branch vertex
above the distinguished block `A₀`, which is the core's
`LimitChainCore.GraphData`, and with it `LimitChainCore.GraphData.equivalence`
-- the member's stable incidence graph identified with the incoming one.

## Where each member's branch vertex sits

Above `A₀` the incoming source vertex is trivalent, carrying `e₁`, `e₂` (both
above `t₂ = doubleLabel`) and `e₃` (above `t₃ = singleLabel`); Cardinality M
puts the dangling `e₄` above `t₃` as well
(`W2MkkSourceCandidates.Shape.deleted_single`).  The flag dictionary is read
off `W2MkkStableGraph`'s census, never off a cardinality:

* a **detaching member** `M⁽¹⁾`/`M⁽²⁾` (`selectedSide = true`, the **`t₃`
  endpoint**).  Its `t₂` endpoints, one per endpoint block, are divalent
  (`detach_nonDanglingValency_old`); its `t₃` endpoint over `{x}` is entirely
  pruned, since the new occurrence through the pinned sheet dies with `e₄`
  (`detach_new_pin_dangling`); its `t₃` endpoint over `A⁽ᵠ⁾ = A₀ ∖ {x}` carries
  the retained `e₃` and both surviving regrown occurrences and is the branch
  vertex (`detach_nonDanglingIncident_fresh`).  Its flag retains `e₃` and sends
  each `t₂` occurrence to the regrown occurrence of its own endpoint block.
* `M⁽³⁾` (`selectedSide = false`, the **`t₂` endpoint**).  Its `t₃` endpoint is
  divalent, joining the one regrown occurrence to `e₃`
  (`joined_nonDanglingValency_fresh`), and its `t₂` endpoint over the whole of
  `A₀` carries `e₁`, `e₂` and that regrown occurrence
  (`joined_nonDanglingIncident_old`): the branch vertex.  Its flag retains `e₁`
  and `e₂` and sends `e₃` to the regrown occurrence.

## The anchor

`LimitChainCore.GraphData` reads the branch vertex above the expanded endpoint
of the bundle's own anchor `selected`, which `W2MkkStableLift`'s background
shapes take to be the wall block's canonical representative `block.1`.  For
`M⁽³⁾` that is harmless -- its `t₂` endpoint is the whole wall block -- but a
detaching member separates the pinned sheet `x` on the `t₃` side, and nothing
forbids `block.1` from *being* `x`, in which case the endpoint above `block.1`
is the entirely pruned singleton and no flag dictionary exists there.
`reanchor` moves the anchor to any other sheet of the same wall block; it
changes neither the candidate nor `SelectedData.stablePathEquiv`
(`reanchor_stablePathEquiv` is `rfl`), so the row half of the chain -- and with
it every `W2MkkLimitMatrix` evaluation -- is untouched.  A detaching member is
anchored at `DetachData.remainder`, the sheet Base II.2 uses to name
`A_p ∖ {x}`.

## Discipline

Every endpoint statement below is an identity of **occurrence** sets read off
`W2MkkStableGraph`'s exported census; no stable row is asserted distinct from
another, so a stable loop through a branch vertex is not excluded, and no
cardinality argument replaces the census anywhere.  No hypothesis beyond
`W2MkkSourceCandidates`' bundle (a `W2R2SourceProfile.SourceProfile`, a
`W2MkkSourceCandidates.Shape`, a `DetachData`) and the
`SecondEquation.W2SourceInput` the chain already carries appears.

Member 2 of Figure 34 is not transported here: `M⁽¹⁾` and `M⁽²⁾` are the same
uniform `DetachData.candidate`, and `M⁽²⁾` is obtained by instantiating these
definitions at the branch-swapped datum, exactly as `W2MkkStableLift` records.
-/

namespace DraismaVargas.LocalCases.W2MkkGraphData

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2MkkSourceCandidates
open W2MkkStableGraph W2MkkStableLift W2MkkRowDescent
open LimitChainCore (BackgroundShape LiftData SelectedData GraphData wallSide
  pasted newSourceEdge_eq_iff_rel oldSourceEdge_ne_newSourceEdge
  newSourceEdge_incident_old newSourceEdge_incident_fresh
  sourceEndpoint_old_eq_of_rel sourceEndpoint_fresh_eq_of_rel
  sourceEdge_eq_iff_rel sourceEndpoint_eq_of_rel wallSide_false wallSide_true)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §0  Three occurrence identities

None of these is special to M-kk; they are of the kind collected in
`LimitChainCore` §0 (the occurrence identities for an arbitrary candidate). -/

/-- An occurrence is the canonical occurrence above its own target edge through
its own sheet. -/
theorem sourceEdge_self (data : GluingDatum target degree) (edge : data.SourceEdge) :
    data.sourceEdge edge.1.1 edge.1.2 = edge :=
  Subtype.ext (Prod.ext rfl edge.2)

theorem sourceEdge_of_target {edge : data.SourceEdge} {place : target.edges}
    (hTarget : edge.1.1 = place) : data.sourceEdge place edge.1.2 = edge := by
  subst hTarget
  exact sourceEdge_self data edge

/-- An occurrence incident to a wall endpoint has its sheet in that block. -/
theorem wall_rel_of_incident {edge : data.SourceEdge} {sheet : Fin degree}
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    (data.vertexPartition wall).Rel sheet edge.1.2 :=
  ((data.vertexPartition wall).rel_repr_right sheet).trans
    ((incident_iff_target_mem_and_rel data edge (data.sourceEndpoint wall sheet)).mp
      hIncident).2

/-- Two surviving occurrences with the same underlying occurrence name one
stable row. -/
theorem stablePath_congr {expanded : CFGraph} {datum : GluingDatum expanded degree}
    {first second : NonDanglingEdge datum} (hEqual : first.1 = second.1) :
    NonDanglingEdge.stablePath first = NonDanglingEdge.stablePath second :=
  congrArg NonDanglingEdge.stablePath (Subtype.ext hEqual)

/-- Detaching one sheet leaves every *other* block of its own partition
untouched, so two sheets outside the detached block stay related.  This is a
fact about `Infrastructure.SheetPartition` alone. -/
theorem detachSheet_rel_of_not_rel_local (partition : SheetPartition degree)
    (single remainder first second : Fin degree) (hne : single ≠ remainder)
    (hTogether : partition.Rel single remainder)
    (hFirst : ¬ partition.Rel single first) (hSecond : ¬ partition.Rel single second)
    (hRel : partition.Rel first second) :
    (partition.detachSheet single remainder hne hTogether).Rel first second := by
  show (partition.detachSheet single remainder hne hTogether).repr first =
    (partition.detachSheet single remainder hne hTogether).repr second
  rw [partition.detachSheet_repr_of_not_rel single remainder first hne hTogether hFirst,
    partition.detachSheet_repr_of_not_rel single remainder second hne hTogether hSecond]
  exact hRel

/-! ## §1  Moving the anchor inside the distinguished block -/

/-- **Re-anchor a selected-data bundle at another sheet of the same wall
block.**  Every field of `LimitChainCore.SelectedData` mentions the anchor only
through `(data.vertexPartition wall).Rel selected`, which two sheets of one
block share, so nothing has to be reproved. -/
noncomputable def reanchor (rd : SelectedData data wall) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel rd.selected anchor) :
    SelectedData data wall where
  toWallCandidate := rd.toWallCandidate
  selected := anchor
  left_block := fun hSheet ↦ rd.left_block (fun h ↦ hSheet (hRel.symm.trans h))
  right_block := fun hSheet ↦ rd.right_block (fun h ↦ hSheet (hRel.symm.trans h))
  newEdge_block := fun hSheet ↦ rd.newEdge_block (fun h ↦ hSheet (hRel.symm.trans h))
  genus_eq := rd.genus_eq
  valid := rd.valid
  selected_valency_ne_two := by
    rw [← sourceEndpoint_eq_of_rel data wall hRel]
    exact rd.selected_valency_ne_two
  selectedRep := rd.selectedRep
  selectedRep_survives := fun sheet h ↦ rd.selectedRep_survives sheet (hRel.trans h)
  selectedRep_congr := fun first second h₁ h₂ h₃ ↦
    rd.selectedRep_congr first second (hRel.trans h₁) (hRel.trans h₂) h₃
  selected_new_stablePath := fun sheet h ↦ rd.selected_new_stablePath sheet (hRel.trans h)
  selected_left_pair := by
    intro sheet h hValency
    obtain ⟨other, hOther, hStar⟩ := rd.selected_left_pair sheet (hRel.trans h) hValency
    exact ⟨other, hRel.symm.trans hOther, hStar⟩
  selected_right_pair := by
    intro sheet h hValency
    obtain ⟨other, hOther, hStar⟩ := rd.selected_right_pair sheet (hRel.trans h) hValency
    exact ⟨other, hRel.symm.trans hOther, hStar⟩

@[simp] theorem reanchor_candidate (rd : SelectedData data wall) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel rd.selected anchor) :
    (reanchor rd anchor hRel).candidate = rd.candidate := rfl

@[simp] theorem reanchor_selected (rd : SelectedData data wall) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel rd.selected anchor) :
    (reanchor rd anchor hRel).selected = anchor := rfl

/-- **Re-anchoring does not touch the row half.**  The stable-row bijection is
the retained-occurrence lift, which reads only the candidate. -/
theorem reanchor_stablePathEquiv (rd : SelectedData data wall) (anchor : Fin degree)
    (hRel : (data.vertexPartition wall).Rel rd.selected anchor) :
    (reanchor rd anchor hRel).stablePathEquiv = rd.stablePathEquiv := rfl

/-! ## §2  The incoming surviving star above `A₀` -/

/-- **The distinguished source vertex carries exactly `e₁`, `e₂`, `e₃`.**  The
profile's four occurrences exhaust the star and the fourth one dangles. -/
theorem incoming_star (profile : W2R2SourceProfile.SourceProfile data star block) :
    nonDanglingIncident data (data.sourceEndpoint wall block.1) =
      {profile.first.1, profile.second.1, profile.third.1} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases profile.exhaustive ⟨edge, hIncident⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
    · exfalso
      have hVal : edge = profile.deleted.edge.1 := congrArg Subtype.val h
      rw [hVal] at hSurvives
      exact hSurvives profile.deleted.dangling
  · rintro (rfl | rfl | rfl)
    · exact ⟨profile.first_survives, profile.first.2⟩
    · exact ⟨profile.second_survives, profile.second.2⟩
    · exact ⟨profile.third_survives, profile.third.2⟩

/-- The same star read at any other sheet of the distinguished block. -/
theorem incoming_star_at (profile : W2R2SourceProfile.SourceProfile data star block)
    {anchor : Fin degree} (hRel : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident data (data.sourceEndpoint wall anchor) =
      {profile.first.1, profile.second.1, profile.third.1} := by
  rw [← sourceEndpoint_eq_of_rel data wall hRel]
  exact incoming_star profile

/-- `e₁` is the `t₂` occurrence through its own sheet. -/
theorem first_eq_sourceEdge (profile : W2R2SourceProfile.SourceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (firstSheet profile) =
      profile.first.1 :=
  sourceEdge_of_target profile.first_target

/-- `e₂` is the `t₂` occurrence through its own sheet. -/
theorem second_eq_sourceEdge (profile : W2R2SourceProfile.SourceProfile data star block) :
    data.sourceEdge (star.edge profile.doubleLabel) (secondSheet profile) =
      profile.second.1 :=
  sourceEdge_of_target profile.second_target

/-- `e₁` and `e₂` are distinct occurrences. -/
theorem first_ne_second_edge
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first.1 ≠ profile.second.1 :=
  fun hEqual ↦ profile.first_ne_second (Subtype.ext hEqual)

/-- `e₃` is not above `t₂`. -/
theorem third_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.third.1.1.1 ≠ star.edge profile.doubleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (hTarget.symm.trans profile.third_target))

/-- The two `t₂` survivors lie in different endpoint blocks, so exactly one of
them lies in the pinned sheet's block. -/
theorem endpointPartition_pin_cases (shape : Shape profile) :
    ((endpointPartition profile).Rel (pinSheet profile) (firstSheet profile) ∧
        ¬ (endpointPartition profile).Rel (pinSheet profile) (secondSheet profile)) ∨
      (¬ (endpointPartition profile).Rel (pinSheet profile) (firstSheet profile) ∧
        (endpointPartition profile).Rel (pinSheet profile) (secondSheet profile)) := by
  rcases endpointPartition_covers shape (pinSheet profile) (pinSheet_rel profile) with
    hFirst | hSecond
  · refine Or.inl ⟨hFirst.symm, fun hSecond ↦ ?_⟩
    exact endpointPartition_separate profile (hFirst.trans hSecond)
  · refine Or.inr ⟨fun hFirst ↦ ?_, hSecond.symm⟩
    exact endpointPartition_separate profile (hSecond.trans hFirst).symm

/-- Off the pinned endpoint block a sheet of `A₀` lies in `otherSheet`'s
block. -/
theorem otherSheet_rel_of_not_rel (shape : Shape profile) {sheet : Fin degree}
    (hBlock : (data.vertexPartition wall).Rel block.1 sheet)
    (hEp : ¬ (endpointPartition profile).Rel (pinSheet profile) sheet) :
    (endpointPartition profile).Rel (otherSheet profile) sheet := by
  classical
  rcases endpointPartition_pin_cases shape with ⟨hFirst, _⟩ | ⟨hFirst, hSecond⟩
  · have hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) :=
      hFirst.symm
    have hOther : otherSheet profile = secondSheet profile := by
      simp only [otherSheet, hPin, ↓reduceIte]
    rcases endpointPartition_covers shape sheet hBlock with hCover | hCover
    · exact absurd (hFirst.trans hCover) hEp
    · rw [hOther]; exact hCover
  · have hPin : ¬ (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) :=
      fun h ↦ hFirst h.symm
    have hOther : otherSheet profile = firstSheet profile := by
      simp only [otherSheet, hPin, ↓reduceIte]
    rcases endpointPartition_covers shape sheet hBlock with hCover | hCover
    · rw [hOther]; exact hCover
    · exact absurd (hSecond.trans hCover) hEp

/-! ## §3  The detaching member's branch flag

Its branch vertex is the `t₃` endpoint over `A⁽ᵠ⁾ = A₀ ∖ {x}`, so the member is
anchored at `DetachData.remainder`.  The flag retains `e₃` and sends a `t₂`
occurrence to the regrown occurrence of its own endpoint block, which is the
regrown occurrence through its own sheet once that sheet is moved off the
pin. -/

/-- The sheet carrying the regrown partner of a `t₂` occurrence: its own,
moved off the pinned sheet to `DetachData.remainder`. -/
noncomputable def movedSheet (detach : DetachData profile) (sheet : Fin degree) :
    Fin degree :=
  if sheet = pinSheet profile then detach.remainder else sheet

theorem movedSheet_pin (detach : DetachData profile) :
    movedSheet detach (pinSheet profile) = detach.remainder := if_pos rfl

theorem movedSheet_of_ne (detach : DetachData profile) {sheet : Fin degree}
    (hNe : sheet ≠ pinSheet profile) : movedSheet detach sheet = sheet := if_neg hNe

theorem movedSheet_ne_pin (detach : DetachData profile) (sheet : Fin degree) :
    movedSheet detach sheet ≠ pinSheet profile := by
  by_cases hSheet : sheet = pinSheet profile
  · rw [hSheet, movedSheet_pin]
    exact fun hEqual ↦ detach.ne_remainder hEqual.symm
  · rw [movedSheet_of_ne detach hSheet]
    exact hSheet

theorem movedSheet_wall_rel (detach : DetachData profile) {sheet : Fin degree}
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet) :
    (data.vertexPartition wall).Rel (pinSheet profile) (movedSheet detach sheet) := by
  by_cases hSheet : sheet = pinSheet profile
  · rw [hSheet, movedSheet_pin]
    exact detach.wallTogether
  · rw [movedSheet_of_ne detach hSheet]
    exact hWall

/-- Moving a sheet off the pin does not change which `t₂` occurrence it names:
the pin and `DetachData.remainder` lie in one `t₂` block. -/
theorem sourceEdge_movedSheet (detach : DetachData profile) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    data.sourceEdge (star.edge profile.doubleLabel) (movedSheet detach edge.1.2) = edge := by
  by_cases hPin : edge.1.2 = pinSheet profile
  · rw [hPin, movedSheet_pin]
    refine Eq.trans ((sourceEdge_eq_iff_rel data (star.edge profile.doubleLabel)
      detach.remainder (pinSheet profile)).mpr detach.together.symm) ?_
    rw [← hPin]
    exact sourceEdge_of_target hTarget
  · rw [movedSheet_of_ne detach hPin]
    exact sourceEdge_of_target hTarget

/-- **The branch flag of a detaching member.** -/
noncomputable def detachFlag (shape : Shape profile) (detach : DetachData profile)
    (edge : data.SourceEdge) : (detach.candidate shape).datum.SourceEdge :=
  if edge.1.1 = star.edge profile.doubleLabel then
    (detach.candidate shape).newSourceEdge (movedSheet detach edge.1.2)
  else (detach.candidate shape).oldSourceEdge edge

theorem detachFlag_double (shape : Shape profile) (detach : DetachData profile)
    {edge : data.SourceEdge} (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    detachFlag shape detach edge =
      (detach.candidate shape).newSourceEdge (movedSheet detach edge.1.2) := if_pos hTarget

theorem detachFlag_not_double (shape : Shape profile) (detach : DetachData profile)
    {edge : data.SourceEdge} (hTarget : ¬ edge.1.1 = star.edge profile.doubleLabel) :
    detachFlag shape detach edge = (detach.candidate shape).oldSourceEdge edge :=
  if_neg hTarget

/-- Inside the pinned endpoint block every sheet names the regrown occurrence
over `A_p ∖ {x}`. -/
theorem newSourceEdge_movedSheet_of_rel (shape : Shape profile) (detach : DetachData profile)
    {sheet : Fin degree}
    (hEp : (endpointPartition profile).Rel (pinSheet profile) sheet) :
    (detach.candidate shape).newSourceEdge (movedSheet detach sheet) =
      (detach.candidate shape).newSourceEdge detach.remainder := by
  by_cases hSheet : sheet = pinSheet profile
  · rw [hSheet, movedSheet_pin]
  · rw [movedSheet_of_ne detach hSheet]
    refine (newSourceEdge_eq_iff_rel sheet detach.remainder).mpr ?_
    refine (detach_pasted_newEdge_rel_iff shape detach sheet detach.remainder
      ((endpointPartition_refines profile).rel hEp)).mpr ?_
    exact W3ShiftSourceCandidates.detachSheet_rel_remainder (endpointPartition profile)
      (pinSheet profile) detach.remainder sheet detach.ne_remainder detach.together hEp hSheet

/-- Outside it every sheet of `A₀` names the regrown occurrence over `A_q`. -/
theorem newSourceEdge_movedSheet_of_not_rel (shape : Shape profile)
    (detach : DetachData profile) {sheet : Fin degree}
    (hBlock : (data.vertexPartition wall).Rel block.1 sheet)
    (hEp : ¬ (endpointPartition profile).Rel (pinSheet profile) sheet) :
    (detach.candidate shape).newSourceEdge (movedSheet detach sheet) =
      (detach.candidate shape).newSourceEdge (otherSheet profile) := by
  have hSheet : sheet ≠ pinSheet profile := by
    intro hEqual
    exact hEp (((endpointPartition profile).rel_iff _ _).mpr (by rw [hEqual]))
  rw [movedSheet_of_ne detach hSheet]
  refine (newSourceEdge_eq_iff_rel sheet (otherSheet profile)).mpr ?_
  refine (detach_pasted_newEdge_rel_iff shape detach sheet (otherSheet profile)
    ((pinSheet_rel profile).symm.trans hBlock)).mpr ?_
  exact detachSheet_rel_of_not_rel_local (endpointPartition profile) (pinSheet profile)
    detach.remainder sheet (otherSheet profile) detach.ne_remainder detach.together hEp
    (otherSheet_not_rel profile) (otherSheet_rel_of_not_rel shape hBlock hEp).symm

/-- **The two `t₂` survivors go to the member's two regrown occurrences**, in
whichever order the pinned sheet's endpoint block dictates. -/
theorem detach_flag_pair (shape : Shape profile) (detach : DetachData profile) :
    (detachFlag shape detach profile.first.1 =
          (detach.candidate shape).newSourceEdge detach.remainder ∧
        detachFlag shape detach profile.second.1 =
          (detach.candidate shape).newSourceEdge (otherSheet profile)) ∨
      (detachFlag shape detach profile.first.1 =
          (detach.candidate shape).newSourceEdge (otherSheet profile) ∧
        detachFlag shape detach profile.second.1 =
          (detach.candidate shape).newSourceEdge detach.remainder) := by
  have hFirstFlag := detachFlag_double shape detach profile.first_target
  have hSecondFlag := detachFlag_double shape detach profile.second_target
  rcases endpointPartition_pin_cases shape with ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩
  · refine Or.inl ⟨hFirstFlag.trans ?_, hSecondFlag.trans ?_⟩
    · exact newSourceEdge_movedSheet_of_rel shape detach hFirst
    · exact newSourceEdge_movedSheet_of_not_rel shape detach (secondSheet_rel profile) hSecond
  · refine Or.inr ⟨hFirstFlag.trans ?_, hSecondFlag.trans ?_⟩
    · exact newSourceEdge_movedSheet_of_not_rel shape detach (firstSheet_rel profile) hFirst
    · exact newSourceEdge_movedSheet_of_rel shape detach hSecond

/-- The member's two regrown occurrences are distinct: one lies over
`A_p ∖ {x}`, the other over `A_q`. -/
theorem detach_new_remainder_ne_other (shape : Shape profile) (detach : DetachData profile) :
    (detach.candidate shape).newSourceEdge detach.remainder ≠
      (detach.candidate shape).newSourceEdge (otherSheet profile) :=
  detach_newSourceEdge_ne shape detach detach.remainder (otherSheet profile)
    detach.wallTogether detach.together (otherSheet_not_rel profile)

theorem detach_flag_distinct (shape : Shape profile) (detach : DetachData profile) :
    detachFlag shape detach profile.first.1 ≠ detachFlag shape detach profile.second.1 ∧
      detachFlag shape detach profile.first.1 ≠ detachFlag shape detach profile.third.1 ∧
      detachFlag shape detach profile.second.1 ≠ detachFlag shape detach profile.third.1 := by
  have hThird := detachFlag_not_double shape detach (third_target_ne profile)
  have hNeOther := detach_new_remainder_ne_other shape detach
  rcases detach_flag_pair shape detach with ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hFirst, hSecond]; exact hNeOther
    · rw [hFirst, hThird]; exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)
    · rw [hSecond, hThird]; exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)
  · refine ⟨?_, ?_, ?_⟩
    · rw [hFirst, hSecond]; exact Ne.symm hNeOther
    · rw [hFirst, hThird]; exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)
    · rw [hSecond, hThird]; exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)

/-! ### The three `GraphData` fields at the detaching branch vertex -/

/-- **The flag dictionary at the branch vertex.**  Read off
`detach_nonDanglingIncident_fresh` and the incoming star, not off a
cardinality. -/
theorem detach_selectedFlag_star (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    nonDanglingIncident (detach.candidate shape).datum
        ((detach.candidate shape).datum.sourceEndpoint (freshVertex target)
          detach.remainder) =
      (nonDanglingIncident data (data.sourceEndpoint wall detach.remainder)).image
        (detachFlag shape detach) := by
  classical
  have hBlock : (data.vertexPartition wall).Rel block.1 detach.remainder :=
    (pinSheet_rel profile).trans detach.wallTogether
  have hThird := detachFlag_not_double shape detach (third_target_ne profile)
  rw [detach_nonDanglingIncident_fresh input shape detach detach.remainder
      detach.wallTogether (Ne.symm detach.ne_remainder),
    incoming_star_at profile hBlock]
  rcases detach_flag_pair shape detach with ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩ <;>
    · simp only [Finset.image_insert, Finset.image_singleton, hFirst, hSecond, hThird]
      ext edge
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto

theorem detach_selectedFlag_injOn (shape : Shape profile) (detach : DetachData profile) :
    Set.InjOn (detachFlag shape detach)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall detach.remainder)) := by
  classical
  have hBlock : (data.vertexPartition wall).Rel block.1 detach.remainder :=
    (pinSheet_rel profile).trans detach.wallTogether
  obtain ⟨h12, h13, h23⟩ := detach_flag_distinct shape detach
  rw [incoming_star_at profile hBlock]
  intro first hFirst second hSecond hEqual
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hFirst hSecond
  rcases hFirst with rfl | rfl | rfl <;> rcases hSecond with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd hEqual h12
      | exact absurd hEqual.symm h12
      | exact absurd hEqual h13
      | exact absurd hEqual.symm h13
      | exact absurd hEqual h23
      | exact absurd hEqual.symm h23

/-- **Every other expanded endpoint above `A₀` is divalent or entirely
pruned.**  The `t₂` endpoints are divalent, the `t₃` endpoint over `{x}` is
empty, and every other `t₃` endpoint *is* the branch vertex. -/
theorem detach_selected_not_branch (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (side : Bool) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel detach.remainder sheet)
    (hNotBranch : (detach.candidate shape).datum.sourceEndpoint
        (wallSide target wall side) sheet ≠
      (detach.candidate shape).datum.sourceEndpoint (wallSide target wall true)
        detach.remainder) :
    nonDanglingValency (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (wallSide target wall side) sheet) ≤ 2 := by
  have hPin : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    detach.wallTogether.trans hRel
  cases side with
  | false =>
      simp only [wallSide_false] at hNotBranch ⊢
      by_cases hSheet : sheet = pinSheet profile
      · have hVertex : (detach.candidate shape).datum.sourceEndpoint
            (oldVertex target wall) sheet =
            (detach.candidate shape).datum.sourceEndpoint (oldVertex target wall)
              detach.remainder := by
          rw [hSheet]
          exact sourceEndpoint_old_eq_of_rel _ _
            (detach_pasted_left_rel shape detach _ _ rfl detach.together)
        rw [hVertex]
        have := detach_nonDanglingValency_old input shape detach detach.remainder
          detach.wallTogether (Ne.symm detach.ne_remainder)
        omega
      · have := detach_nonDanglingValency_old input shape detach sheet hPin hSheet
        omega
  | true =>
      simp only [wallSide_true] at hNotBranch ⊢
      by_cases hSheet : sheet = pinSheet profile
      · rw [hSheet]
        have := detach_nonDanglingValency_fresh_pin input shape detach
        omega
      · exact absurd (detach_fresh_vertex_eq shape detach sheet detach.remainder hPin hSheet
          detach.wallTogether (Ne.symm detach.ne_remainder)) hNotBranch

/-- **The flag preserves stable rows.**  A retained `e₃` keeps its own row; a
`t₂` occurrence and its regrown partner are consecutive at the divalent `t₂`
endpoint (`detach_new_stablePath_eq`). -/
theorem detach_selectedFlag_row (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall detach.remainder))
    (hFlag : ¬ IsDangling (detach.candidate shape).datum (detachFlag shape detach edge)) :
    NonDanglingEdge.stablePath (⟨detachFlag shape detach edge, hFlag⟩ :
        NonDanglingEdge (detach.candidate shape).datum) =
      (retainedEdge (detach.candidate shape) input.valid.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)).stablePath := by
  by_cases hTarget : edge.1.1 = star.edge profile.doubleLabel
  · have hWallEdge : (data.vertexPartition wall).Rel (pinSheet profile) edge.1.2 :=
      detach.wallTogether.trans (wall_rel_of_incident hIncident)
    have hMovedWall := movedSheet_wall_rel detach hWallEdge
    have hMovedNe := movedSheet_ne_pin detach edge.1.2
    have hRow := detach_new_stablePath_eq input shape detach (movedSheet detach edge.1.2)
      hMovedWall hMovedNe
    refine Eq.trans ?_ (Eq.trans hRow ?_)
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (detachFlag_double shape detach hTarget))
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (congrArg (detach.candidate shape).oldSourceEdge
          (sourceEdge_movedSheet detach hTarget)))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (detachFlag_not_double shape detach hTarget))

/-- **Figure 34's detaching member as the core's `GraphData`.**  `selectedSide`
is `true`: its branch vertex is the `t₃` endpoint over `A₀ ∖ {x}`, of surviving
valency three. -/
noncomputable def detachGraphData (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) : GraphData data wall where
  toSelectedData := reanchor (detachSelectedData input shape detach) detach.remainder
    ((pinSheet_rel profile).trans detach.wallTogether)
  selectedSide := true
  selectedFlag := detachFlag shape detach
  selectedFlag_star := detach_selectedFlag_star input shape detach
  selectedFlag_injOn := detach_selectedFlag_injOn shape detach
  selected_not_branch := detach_selected_not_branch input shape detach
  selectedFlag_row := detach_selectedFlag_row input shape detach

@[simp] theorem detachGraphData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachGraphData input shape detach).candidate = detach.candidate shape := rfl

@[simp] theorem detachGraphData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachGraphData input shape detach).selected = detach.remainder := rfl

@[simp] theorem detachGraphData_selectedSide (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachGraphData input shape detach).selectedSide = true := rfl

/-- Re-anchoring left the row half alone, so the member's stable-row bijection
is still `W2MkkRowDescent.detachStablePathEquiv`. -/
theorem detachGraphData_stablePathEquiv (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachGraphData input shape detach).stablePathEquiv =
      detachStablePathEquiv input shape detach := rfl

/-! ## §4  `M⁽³⁾`'s branch flag

Base II.1.M keeps the whole of `A₀` on both sides, so `M⁽³⁾` needs no
re-anchoring: its branch vertex is the `t₂` endpoint above the anchor
`block.1` itself, carrying `e₁`, `e₂` and the single regrown occurrence. -/

/-- `e₁` is not above `t₃`. -/
theorem first_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first.1.1.1 ≠ star.edge profile.singleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (profile.first_target.symm.trans hTarget))

/-- `e₂` is not above `t₃`. -/
theorem second_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.second.1.1.1 ≠ star.edge profile.singleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (profile.second_target.symm.trans hTarget))

/-- The anchor is related to itself. -/
theorem block_rel_self (data : GluingDatum target degree) (wall : target.V)
    (block : WallBlock data wall) :
    (data.vertexPartition wall).Rel block.1 block.1 :=
  ((data.vertexPartition wall).rel_iff _ _).mpr rfl

/-- **The branch flag of `M⁽³⁾`.**  `e₁` and `e₂` are retained; `e₃` goes to the
single regrown occurrence above `A₀`. -/
noncomputable def joinedFlag (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) (edge : data.SourceEdge) :
    (joinedCandidate profile distinguished).datum.SourceEdge :=
  if edge.1.1 = star.edge profile.singleLabel then
    (joinedCandidate profile distinguished).newSourceEdge block.1
  else (joinedCandidate profile distinguished).oldSourceEdge edge

theorem joinedFlag_single (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    joinedFlag profile distinguished edge =
      (joinedCandidate profile distinguished).newSourceEdge block.1 := if_pos hTarget

theorem joinedFlag_not_single (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) {edge : data.SourceEdge}
    (hTarget : ¬ edge.1.1 = star.edge profile.singleLabel) :
    joinedFlag profile distinguished edge =
      (joinedCandidate profile distinguished).oldSourceEdge edge := if_neg hTarget

/-- **The flag dictionary at `M⁽³⁾`'s branch vertex.** -/
theorem joined_selectedFlag_star (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    nonDanglingIncident (joinedCandidate profile distinguished).datum
        ((joinedCandidate profile distinguished).datum.sourceEndpoint
          (oldVertex target wall) block.1) =
      (nonDanglingIncident data (data.sourceEndpoint wall block.1)).image
        (joinedFlag profile distinguished) := by
  classical
  have hFirst := joinedFlag_not_single profile distinguished (first_target_ne profile)
  have hSecond := joinedFlag_not_single profile distinguished (second_target_ne profile)
  have hThird := joinedFlag_single profile distinguished profile.third_target
  rw [joined_nonDanglingIncident_old input shape distinguished block.1
      (block_rel_self data wall block),
    incoming_star profile]
  simp only [Finset.image_insert, Finset.image_singleton, hFirst, hSecond, hThird]

theorem joined_flag_distinct (profile : W2R2SourceProfile.SourceProfile data star block)
    (distinguished : Fin degree) :
    joinedFlag profile distinguished profile.first.1 ≠
        joinedFlag profile distinguished profile.second.1 ∧
      joinedFlag profile distinguished profile.first.1 ≠
        joinedFlag profile distinguished profile.third.1 ∧
      joinedFlag profile distinguished profile.second.1 ≠
        joinedFlag profile distinguished profile.third.1 := by
  have hFirst := joinedFlag_not_single profile distinguished (first_target_ne profile)
  have hSecond := joinedFlag_not_single profile distinguished (second_target_ne profile)
  have hThird := joinedFlag_single profile distinguished profile.third_target
  refine ⟨?_, ?_, ?_⟩
  · rw [hFirst, hSecond]
    exact fun hEqual ↦ first_ne_second_edge profile
      (ResolutionCut.oldSourceEdge_injective _ hEqual)
  · rw [hFirst, hThird]
    exact oldSourceEdge_ne_newSourceEdge _ _
  · rw [hSecond, hThird]
    exact oldSourceEdge_ne_newSourceEdge _ _

theorem joined_selectedFlag_injOn
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    Set.InjOn (joinedFlag profile distinguished)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall block.1)) := by
  classical
  obtain ⟨h12, h13, h23⟩ := joined_flag_distinct profile distinguished
  rw [incoming_star profile]
  intro first hFirst second hSecond hEqual
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hFirst hSecond
  rcases hFirst with rfl | rfl | rfl <;> rcases hSecond with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd hEqual h12
      | exact absurd hEqual.symm h12
      | exact absurd hEqual h13
      | exact absurd hEqual.symm h13
      | exact absurd hEqual h23
      | exact absurd hEqual.symm h23

/-- **Every other expanded endpoint above `A₀` is divalent.**  `M⁽³⁾`'s `t₃`
endpoint is divalent and every `t₂` endpoint above `A₀` *is* the branch
vertex. -/
theorem joined_selected_not_branch (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (side : Bool) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hNotBranch : (joinedCandidate profile distinguished).datum.sourceEndpoint
        (wallSide target wall side) sheet ≠
      (joinedCandidate profile distinguished).datum.sourceEndpoint
        (wallSide target wall false) block.1) :
    nonDanglingValency (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (wallSide target wall side) sheet) ≤ 2 := by
  cases side with
  | false =>
      simp only [wallSide_false] at hNotBranch ⊢
      exact absurd (joined_old_vertex_eq profile distinguished sheet block.1 hRel.symm)
        hNotBranch
  | true =>
      simp only [wallSide_true] at hNotBranch ⊢
      have := joined_nonDanglingValency_fresh input shape distinguished sheet hRel
      omega

/-- **The flag preserves stable rows.**  `e₁` and `e₂` are retained; `e₃` and
the regrown occurrence are consecutive at the divalent `t₃` endpoint
(`joined_new_stablePath_eq_third`). -/
theorem joined_selectedFlag_row (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall block.1))
    (hFlag : ¬ IsDangling (joinedCandidate profile distinguished).datum
      (joinedFlag profile distinguished edge)) :
    NonDanglingEdge.stablePath (⟨joinedFlag profile distinguished edge, hFlag⟩ :
        NonDanglingEdge (joinedCandidate profile distinguished).datum) =
      (retainedEdge (joinedCandidate profile distinguished) input.valid.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)).stablePath := by
  classical
  by_cases hTarget : edge.1.1 = star.edge profile.singleLabel
  · have hMem : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall block.1) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvives, hIncident⟩
    rw [incoming_star profile] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    have hThird : edge = profile.third.1 := by
      rcases hMem with rfl | rfl | rfl
      · exact absurd hTarget (first_target_ne profile)
      · exact absurd hTarget (second_target_ne profile)
      · rfl
    subst hThird
    have hRow := joined_new_stablePath_eq_third input shape distinguished block.1
      (block_rel_self data wall block)
    refine Eq.trans ?_ hRow
    exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (joinedFlag_single profile distinguished hTarget))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (joinedFlag_not_single profile distinguished hTarget))

/-- **Figure 34's `M⁽³⁾` as the core's `GraphData`.**  `selectedSide` is
`false`: its branch vertex is the `t₂` endpoint above `A₀`. -/
noncomputable def joinedGraphData (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) : GraphData data wall where
  toSelectedData := joinedSelectedData input shape distinguished
  selectedSide := false
  selectedFlag := joinedFlag profile distinguished
  selectedFlag_star := joined_selectedFlag_star input shape distinguished
  selectedFlag_injOn := joined_selectedFlag_injOn profile distinguished
  selected_not_branch := joined_selected_not_branch input shape distinguished
  selectedFlag_row := joined_selectedFlag_row input shape distinguished

@[simp] theorem joinedGraphData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedGraphData input shape distinguished).candidate =
      joinedCandidate profile distinguished := rfl

@[simp] theorem joinedGraphData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedGraphData input shape distinguished).selected = block.1 := rfl

@[simp] theorem joinedGraphData_selectedSide (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedGraphData input shape distinguished).selectedSide = false := rfl

theorem joinedGraphData_stablePathEquiv (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedGraphData input shape distinguished).stablePathEquiv =
      joinedStablePathEquiv input shape distinguished := rfl

/-! ## §5  The two stable incidence graphs -/

/-- **A detaching member's stable incidence graph is the incoming one.** -/
noncomputable def detachEquivalence (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    StableGraphIncidence.Equivalence data (detach.candidate shape).datum :=
  (detachGraphData input shape detach).equivalence

/-- **Its row map is literally `W2MkkRowDescent`'s bijection**, so every
`W2MkkLimitMatrix` evaluation reads the same rows this dictionary does. -/
theorem detachEquivalence_rowEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    (detachEquivalence input shape detach).row =
      detachStablePathEquiv input shape detach := rfl

@[simp] theorem detachEquivalence_row (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) :
    (detachEquivalence input shape detach).row path =
      detachStablePathEquiv input shape detach path := rfl

/-- **`M⁽³⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def joinedEquivalence (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    StableGraphIncidence.Equivalence data (joinedCandidate profile distinguished).datum :=
  (joinedGraphData input shape distinguished).equivalence

theorem joinedEquivalence_rowEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    (joinedEquivalence input shape distinguished).row =
      joinedStablePathEquiv input shape distinguished := rfl

@[simp] theorem joinedEquivalence_row (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    (joinedEquivalence input shape distinguished).row path =
      joinedStablePathEquiv input shape distinguished path := rfl

/-- Path ends transport to a detaching member. -/
theorem detach_hasPathEnds (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (hEnds : HasPathEnds data) :
    HasPathEnds (detach.candidate shape).datum :=
  (detachGraphData input shape detach).hasPathEnds hEnds

/-- Path ends transport to `M⁽³⁾`. -/
theorem joined_hasPathEnds (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (hEnds : HasPathEnds data) :
    HasPathEnds (joinedCandidate profile distinguished).datum :=
  (joinedGraphData input shape distinguished).hasPathEnds hEnds

end DraismaVargas.LocalCases.W2MkkGraphData
