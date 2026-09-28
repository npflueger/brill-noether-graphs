import DraismaVargas.LocalCases.W2PRowDescent

/-!
# Figure 35's stable incidence graph

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35.

`W2PStableLift` reads a Figure 35 member as the core's
`LimitChainCore.SelectedData`, and `W2PRowDescent` turns that into the
member's geometric stable-row bijection.  What the certified exit also needs
is the **branch half**: a flag dictionary at the member's own
branch vertex above the distinguished block `A₀`, which is the core's
`LimitChainCore.GraphData`, and with it
`LimitChainCore.GraphData.equivalence` -- the stable incidence graph of the
member identified with the incoming one.

## Where each member's branch vertex sits

The incoming source vertex above `A₀` is trivalent, carrying `e₁`, `e₂` (both
above `t₂`) and `e₃` (above `t₃`); Cardinality P puts the dangling `e₄` above
`t₂` as well (`W2PSourceCandidates.Shape`).  The three members place the
surviving trivalent vertex differently, and the flag dictionary is read off
the census, never off a cardinality:

* `M⁽¹⁾` and `M⁽²⁾` (`selectedSide = true`, the **`t₃` endpoint**).  The `t₂`
  side splits into the merged block, trivalent with the dangling `e₄` and
  therefore of surviving valency two, and the untouched block, divalent.  The
  `t₃` endpoint keeps the whole of `A₀` and carries the two regrown
  occurrences together with `e₃`, all three surviving: the branch vertex.  Its
  flag sends `e₁` and `e₂` to the regrown occurrences of their own fine blocks
  and retains `e₃`.
* `M⁽³⁾` (`selectedSide = false`, the **`t₂` endpoint**).  The `t₂` side splits
  into `A₀ ∖ {x}`, carrying `e₁`, `e₂` and the surviving regrown occurrence,
  and the dangling singleton `{x}`, entirely pruned; the `t₃` endpoint is
  divalent, joining the surviving regrown occurrence to `e₃`.  The branch
  vertex is the first `t₂` endpoint, and its flag retains `e₁` and `e₂` and
  sends `e₃` to the regrown occurrence.

## The anchor

`LimitChainCore.GraphData` reads the branch vertex above the expanded endpoint
of the bundle's own anchor `selected`, which `W2PStableLift.backgroundShape`
takes to be the wall block's canonical representative `block.1`.  For `M⁽¹⁾`
and `M⁽²⁾` that is harmless -- the `t₃` endpoint is the whole wall block -- but
for `M⁽³⁾` the `t₂` side separates the dangling sheet, and nothing forbids
`block.1` from *being* that sheet, in which case the endpoint above `block.1`
is the entirely pruned singleton and no flag dictionary exists there.
`reanchor` moves the anchor to any other sheet of the same wall block; it
changes neither the candidate nor `SelectedData.stablePathEquiv`
(`reanchor_stablePathEquiv` is `rfl`), so the row half of the chain is
untouched.  `M⁽³⁾` is anchored at `W2PSourceCandidates.firstSheet`.

## Discipline

Every endpoint statement below is an identity of **occurrence** sets, read off
`W2PSurvival`'s exported census lemmas; no stable row is asserted distinct from
another, so a stable loop through a branch vertex is not excluded.  No
hypothesis beyond `W2PSourceCandidates`' bundle (a
`W2R2SourceProfile.SourceProfile`, a `W2PSourceCandidates.Shape`) and the
`SecondEquation.W2SourceInput` the chain already carries appears anywhere.
-/

namespace DraismaVargas.LocalCases.W2PGraphData

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates
open W2PSurvival W2PStableLift W2PRowDescent
open LimitChainCore (BackgroundShape LiftData SelectedData GraphData wallSide)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

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
    rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall hRel]
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
profile's four occurrences exhaust the star, and the fourth one dangles. -/
theorem incoming_star :
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

/-- The same star with the two `t₂` survivors in the other order. -/
theorem incoming_star_swap :
    nonDanglingIncident data (data.sourceEndpoint wall block.1) =
      {profile.second.1, profile.first.1, profile.third.1} :=
  incoming_star.trans (Finset.insert_comm _ _ _)

/-- `e₃`'s sheet lies in the distinguished block. -/
theorem third_sheet_rel : (data.vertexPartition wall).Rel block.1 profile.third.1.1.2 :=
  sheet_rel_of_incident profile.third

/-- `e₃` is above `t₃`, so it is not above `t₂`. -/
theorem third_target_ne : profile.third.1.1.1 ≠ star.edge profile.doubleLabel := by
  intro h
  exact profile.labels_ne
    (star.edge_injective ((profile.third_target).symm.trans h)).symm

/-! ## §3  The two branch flags -/

/-- **The branch flag of a merging member.**  At the `t₃` endpoint each `t₂`
survivor is replaced by the regrown occurrence of its own fine block; `e₃` is
retained. -/
noncomputable def doubleFlag (member : MemberShape profile) (edge : data.SourceEdge) :
    member.candidate.datum.SourceEdge :=
  if edge.1.1 = star.edge profile.doubleLabel then
    member.candidate.newSourceEdge edge.1.2
  else member.candidate.oldSourceEdge edge

theorem doubleFlag_double (member : MemberShape profile) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    doubleFlag member edge = member.candidate.newSourceEdge edge.1.2 := if_pos hTarget

theorem doubleFlag_single (member : MemberShape profile) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    doubleFlag member edge = member.candidate.oldSourceEdge edge :=
  if_neg (fun h ↦ profile.labels_ne
    (star.edge_injective (hTarget.symm.trans h)).symm)

/-- **The branch flag of the third member.**  At the `t₂` endpoint
above `A₀ ∖ {x}` the occurrences `e₁`, `e₂` are retained and `e₃` is replaced
by the surviving regrown occurrence. -/
noncomputable def singleFlag (member : MemberShape profile) (anchor : Fin degree)
    (edge : data.SourceEdge) : member.candidate.datum.SourceEdge :=
  if edge.1.1 = star.edge profile.singleLabel then
    member.candidate.newSourceEdge anchor
  else member.candidate.oldSourceEdge edge

theorem singleFlag_single (member : MemberShape profile) (anchor : Fin degree)
    {edge : data.SourceEdge} (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    singleFlag member anchor edge = member.candidate.newSourceEdge anchor := if_pos hTarget

theorem singleFlag_double (member : MemberShape profile) (anchor : Fin degree)
    {edge : data.SourceEdge} (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    singleFlag member anchor edge = member.candidate.oldSourceEdge edge :=
  if_neg (fun h ↦ profile.labels_ne (star.edge_injective (hTarget.symm.trans h)))

/-! ## §4  `M⁽¹⁾` and `M⁽²⁾`: the branch vertex is the `t₃` endpoint -/

/-- The occurrence data both merging Figure 35 members are built from: the
`t₂` survivor whose block absorbs the dangling sheet, and the other one.  It is
`W2PSurvival.mergeCensus`'s hypothesis list, with the incoming surviving star
named in the same order. -/
structure MergeInput (profile : W2R2SourceProfile.SourceProfile data star block) where
  /-- The `t₂` survivor whose fine block absorbs the dangling sheet. -/
  own : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  /-- The untouched `t₂` survivor. -/
  other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  own_target : own.1.1.1 = star.edge profile.doubleLabel
  other_target : other.1.1.1 = star.edge profile.doubleLabel
  own_survives : ¬ IsDangling data own.1
  other_survives : ¬ IsDangling data other.1
  own_extra : ¬ (endpointPartition profile).Rel own.1.1.2 (extraSheet profile)
  other_extra : ¬ (endpointPartition profile).Rel other.1.1.2 (extraSheet profile)
  separate : ¬ (endpointPartition profile).Rel own.1.1.2 other.1.1.2
  covers : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel block.1 sheet →
    (endpointPartition profile).Rel own.1.1.2 sheet ∨
      (endpointPartition profile).Rel other.1.1.2 sheet ∨
        (endpointPartition profile).Rel (extraSheet profile) sheet
  /-- The incoming surviving star, in this member's own order. -/
  star_eq : nonDanglingIncident data (data.sourceEndpoint wall block.1) =
    {own.1, other.1, profile.third.1}

namespace MergeInput

variable (m : MergeInput profile)

/-- The member `m` builds. -/
noncomputable def member : MemberShape profile := mergeShape profile m.own m.own_extra

theorem own_rel : (data.vertexPartition wall).Rel block.1 m.own.1.1.2 :=
  sheet_rel_of_incident m.own

theorem other_rel : (data.vertexPartition wall).Rel block.1 m.other.1.1.2 :=
  sheet_rel_of_incident m.other

/-- The member's `t₂` side has exactly two blocks inside `A₀`: `own ∪ {x}` and
`other`. -/
theorem fine_blockCountWithin (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    m.member.fine.blockCountWithin (data.vertexPartition wall) anchor = 2 :=
  blockCountWithin_eq_two _ _ m.own.1.1.2 m.other.1.1.2 anchor
    (hAnchor.symm.trans m.own_rel) (hAnchor.symm.trans m.other_rel)
    (fun sheet hSheet ↦ mergeShape_fine_cover m.own m.other m.own_extra m.covers sheet
      (hAnchor.trans hSheet))
    (mergeShape_fine_not_rel m.own m.other m.own_extra m.other_extra m.separate)

/-- **The `t₃` endpoint above `A₀` is trivalent**: the two regrown occurrences
and `e₃`. -/
theorem fresh_card (shape : Shape profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Fintype.card (IncidentSourceEdge m.member.candidate.datum
      (m.member.candidate.datum.sourceEndpoint (freshVertex target) anchor)) = 3 := by
  rw [m.member.card_incident_fresh_selected shape anchor hAnchor,
    m.fine_blockCountWithin anchor hAnchor]

theorem new_own_survives (shape : Shape profile) (input : W2SourceInput data star) :
    ¬ IsDangling m.member.candidate.datum
      (m.member.candidate.newSourceEdge m.own.1.1.2) :=
  mergeShape_new_own_survives shape input m.own m.own_target m.own_survives m.own_extra

theorem new_other_survives (input : W2SourceInput data star) :
    ¬ IsDangling m.member.candidate.datum
      (m.member.candidate.newSourceEdge m.other.1.1.2) :=
  mergeShape_new_other_survives input m.own m.other m.other_target m.other_survives
    m.own_extra m.other_extra m.separate

theorem new_own_ne_other :
    m.member.candidate.newSourceEdge m.own.1.1.2 ≠
      m.member.candidate.newSourceEdge m.other.1.1.2 := fun h ↦
  mergeShape_fine_not_rel m.own m.other m.own_extra m.other_extra m.separate
    ((m.member.newSourceEdge_eq_iff_fine m.own.1.1.2 m.other.1.1.2 m.own_rel).mp h)

/-- **The branch star.**  Read at any sheet of `A₀`, since the `t₃` endpoint
keeps the whole wall block. -/
theorem fresh_star (shape : Shape profile) (input : W2SourceInput data star)
    (anchor : Fin degree) (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident m.member.candidate.datum
        (m.member.candidate.datum.sourceEndpoint (freshVertex target) anchor) =
      {m.member.candidate.newSourceEdge m.own.1.1.2,
        m.member.candidate.newSourceEdge m.other.1.1.2,
        m.member.candidate.oldSourceEdge profile.third.1} := by
  refine LimitChainCore.nonDanglingIncident_triple_of_card_three _ ?_ ?_ ?_
    m.new_own_ne_other (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
    (m.new_own_survives shape input) (m.new_other_survives input)
    (m.member.retained_survives input ⟨profile.third.1, profile.third_survives⟩)
    (m.fresh_card shape anchor hAnchor)
  · rw [← m.member.sourceEndpoint_fresh_eq_of_rel m.own.1.1.2 anchor
      (m.own_rel.symm.trans hAnchor)]
    exact LimitChainCore.newSourceEdge_incident_fresh (candidate := m.member.candidate) _
  · rw [← m.member.sourceEndpoint_fresh_eq_of_rel m.other.1.1.2 anchor
      (m.other_rel.symm.trans hAnchor)]
    exact LimitChainCore.newSourceEdge_incident_fresh (candidate := m.member.candidate) _
  · exact m.member.single_incident profile.third.1 profile.third_target anchor
      (hAnchor.symm.trans third_sheet_rel)

/-- The dangling `e₄` and the merged survivor are distinct occurrences
upstairs. -/
theorem own_ne_deleted :
    m.member.candidate.oldSourceEdge m.own.1 ≠
      m.member.candidate.oldSourceEdge profile.deleted.edge.1 := by
  intro h
  refine m.own_survives ?_
  rw [ResolutionCut.oldSourceEdge_injective _ h]
  exact profile.deleted.dangling

theorem own_incident :
    Incident m.member.candidate.datum (m.member.candidate.oldSourceEdge m.own.1)
      (m.member.candidate.datum.sourceEndpoint (oldVertex target wall) m.own.1.1.2) :=
  m.member.double_incident_fine m.own.1 m.own_target m.own.1.1.2 m.own_rel rfl

theorem deleted_incident (shape : Shape profile) :
    Incident m.member.candidate.datum
      (m.member.candidate.oldSourceEdge profile.deleted.edge.1)
      (m.member.candidate.datum.sourceEndpoint (oldVertex target wall) m.own.1.1.2) :=
  m.member.double_incident_fine profile.deleted.edge.1 shape.deleted_double m.own.1.1.2
    m.own_rel (mergeShape_fine_rel_extra m.own m.own_extra)

/-- **The merged `t₂` endpoint is not a branch vertex**: it is trivalent with
the dangling `e₄`, so exactly the regrown occurrence and `own` survive. -/
theorem old_own_star (shape : Shape profile) (input : W2SourceInput data star) :
    nonDanglingIncident m.member.candidate.datum
        (m.member.candidate.datum.sourceEndpoint (oldVertex target wall) m.own.1.1.2) =
      {m.member.candidate.newSourceEdge m.own.1.1.2,
        m.member.candidate.oldSourceEdge m.own.1} :=
  LimitChainCore.nonDanglingIncident_pair_of_card_three _
    (LimitChainCore.newSourceEdge_incident_old (candidate := m.member.candidate) m.own.1.1.2)
    m.own_incident (m.deleted_incident shape)
    (Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _))
    (Ne.symm (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)) m.own_ne_deleted
    (m.new_own_survives shape input)
    (m.member.retained_survives input ⟨m.own.1, m.own_survives⟩)
    (m.member.deleted_dangles input) (mergeShape_cardOwn m.own m.own_extra)

/-- The merged block's regrown occurrence joins `own`'s row, through the
trivalent `t₂` endpoint whose third incidence is the dangling `e₄`. -/
theorem new_own_row (shape : Shape profile) (input : W2SourceInput data star) :
    NonDanglingEdge.stablePath
        (⟨m.member.candidate.newSourceEdge m.own.1.1.2, m.new_own_survives shape input⟩ :
          NonDanglingEdge m.member.candidate.datum) =
      (retainedEdge m.member.candidate input.valid.1 ⟨m.own.1, m.own_survives⟩).stablePath :=
  m.member.trivalent_stablePath input _ _
    (LimitChainCore.newSourceEdge_incident_old (candidate := m.member.candidate) m.own.1.1.2)
    m.own_incident _ (m.deleted_incident shape) (m.member.deleted_dangles input)
    (mergeShape_cardOwn m.own m.own_extra)

/-- The untouched block's regrown occurrence joins `other`'s row, through the
divalent `t₂` endpoint. -/
theorem new_other_row (input : W2SourceInput data star) :
    NonDanglingEdge.stablePath
        (⟨m.member.candidate.newSourceEdge m.other.1.1.2, m.new_other_survives input⟩ :
          NonDanglingEdge m.member.candidate.datum) =
      (retainedEdge m.member.candidate input.valid.1 ⟨m.other.1, m.other_survives⟩).stablePath := by
  have hCanonical : data.sourceEdge (star.edge profile.doubleLabel) m.other.1.1.2 = m.other.1 :=
    MemberShape.double_canonical m.other.1 m.other_target
  have hSurvives : ¬ IsDangling data
      (data.sourceEdge (star.edge profile.doubleLabel) m.other.1.1.2) := by
    rw [hCanonical]; exact m.other_survives
  have hRetained : retainedEdge m.member.candidate input.valid.1
        ⟨data.sourceEdge (star.edge profile.doubleLabel) m.other.1.1.2, hSurvives⟩ =
      retainedEdge m.member.candidate input.valid.1 ⟨m.other.1, m.other_survives⟩ :=
    congrArg (retainedEdge m.member.candidate input.valid.1) (Subtype.ext hCanonical)
  rw [← hRetained]
  exact m.member.new_stablePath_eq_double input m.other.1.1.2
    (mergeShape_cardOther m.own m.other m.own_extra m.other_extra m.separate) hSurvives

/-- **The branch flag really is the branch star.** -/
theorem flag_image (shape : Shape profile) (input : W2SourceInput data star) :
    (nonDanglingIncident data (data.sourceEndpoint wall block.1)).image
        (doubleFlag m.member) =
      nonDanglingIncident m.member.candidate.datum
        (m.member.candidate.datum.sourceEndpoint (freshVertex target) block.1) := by
  rw [m.fresh_star shape input block.1 rfl, m.star_eq, Finset.image_insert,
    Finset.image_insert, Finset.image_singleton, doubleFlag_double m.member m.own_target,
    doubleFlag_double m.member m.other_target,
    doubleFlag_single m.member profile.third_target]

theorem fresh_valency (shape : Shape profile) (input : W2SourceInput data star) :
    nonDanglingValency m.member.candidate.datum
      (m.member.candidate.datum.sourceEndpoint (freshVertex target) block.1) = 3 := by
  classical
  rw [← card_nonDanglingIncident, m.fresh_star shape input block.1 rfl,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨m.new_own_ne_other, (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm⟩),
    Finset.card_pair (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm]

theorem flag_injOn (shape : Shape profile) (input : W2SourceInput data star) :
    Set.InjOn (doubleFlag m.member)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall block.1)) := by
  classical
  have hIncoming : nonDanglingValency data (data.sourceEndpoint wall block.1) = 3 :=
    profile.valency
  apply Finset.injOn_of_card_image_eq
  rw [m.flag_image shape input, card_nonDanglingIncident, card_nonDanglingIncident,
    m.fresh_valency shape input, hIncoming]

theorem flag_row (shape : Shape profile) (input : W2SourceInput data star)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall block.1))
    (hFlag : ¬ IsDangling m.member.candidate.datum (doubleFlag m.member edge)) :
    NonDanglingEdge.stablePath
        (⟨doubleFlag m.member edge, hFlag⟩ : NonDanglingEdge m.member.candidate.datum) =
      (retainedEdge m.member.candidate input.valid.1 ⟨edge, hSurvives⟩).stablePath := by
  have hMem : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall block.1) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvives, hIncident⟩
  rw [m.star_eq] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl | rfl
  · exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (doubleFlag_double m.member m.own_target))) (m.new_own_row shape input)
  · exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (doubleFlag_double m.member m.other_target))) (m.new_other_row input)
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (doubleFlag_single m.member profile.third_target))

/-- **Every other expanded endpoint above `A₀` is divalent or pruned.** -/
theorem not_branch (shape : Shape profile) (input : W2SourceInput data star)
    (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hNe : m.member.candidate.datum.sourceEndpoint (wallSide target wall side) sheet ≠
      m.member.candidate.datum.sourceEndpoint (wallSide target wall true) block.1) :
    nonDanglingValency m.member.candidate.datum
      (m.member.candidate.datum.sourceEndpoint (wallSide target wall side) sheet) ≤ 2 := by
  classical
  cases side with
  | true =>
      exact absurd (m.member.sourceEndpoint_fresh_eq_of_rel sheet block.1 hSheet.symm) hNe
  | false =>
      show nonDanglingValency m.member.candidate.datum
        (m.member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2
      rcases mergeShape_fine_cover m.own m.other m.own_extra m.covers sheet hSheet with h | h
      · rw [← m.member.sourceEndpoint_old_eq_of_fine m.own.1.1.2 sheet m.own_rel h,
          ← card_nonDanglingIncident, m.old_own_star shape input,
          Finset.card_pair (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm]
      · rw [← m.member.sourceEndpoint_old_eq_of_fine m.other.1.1.2 sheet m.other_rel h]
        refine le_of_le_of_eq
          (NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge _ _) ?_
        exact mergeShape_cardOther m.own m.other m.own_extra m.other_extra m.separate

end MergeInput

/-- **A merging Figure 35 member's stable incidence data.**  Its branch vertex
is the `t₃` endpoint above `A₀` (`selectedSide = true`), whose complete
surviving star is the two regrown occurrences together with `e₃`; the two `t₂`
endpoints above `A₀` are the merged one, of surviving valency two because `e₄`
dangles there, and the untouched divalent one. -/
noncomputable def mergeGraphData (shape : Shape profile) (input : W2SourceInput data star)
    (m : MergeInput profile) (census : Census input m.member) : GraphData data wall where
  toSelectedData := selectedData input census
  selectedSide := true
  selectedFlag := doubleFlag m.member
  selectedFlag_star := (m.flag_image shape input).symm
  selectedFlag_injOn := m.flag_injOn shape input
  selected_not_branch := fun side sheet hSheet hNe ↦
    m.not_branch shape input side sheet hSheet hNe
  selectedFlag_row := fun edge hSurvives hIncident hFlag ↦
    m.flag_row shape input edge hSurvives hIncident hFlag

@[simp] theorem mergeGraphData_candidate (shape : Shape profile)
    (input : W2SourceInput data star) (m : MergeInput profile)
    (census : Census input m.member) :
    (mergeGraphData shape input m census).candidate = m.member.candidate := rfl

@[simp] theorem mergeGraphData_toSelectedData (shape : Shape profile)
    (input : W2SourceInput data star) (m : MergeInput profile)
    (census : Census input m.member) :
    (mergeGraphData shape input m census).toSelectedData = selectedData input census := rfl

/-- `M⁽¹⁾`'s occurrence data: the dangling sheet joins `e₁`. -/
noncomputable def firstMergeInput (shape : Shape profile) : MergeInput profile where
  own := profile.first
  other := profile.second
  own_target := profile.first_target
  other_target := profile.second_target
  own_survives := profile.first_survives
  other_survives := profile.second_survives
  own_extra := first_extra_separate shape
  other_extra := second_extra_separate shape
  separate := first_second_separate profile
  covers := endpointPartition_covers shape
  star_eq := incoming_star

/-- `M⁽²⁾`'s occurrence data: the dangling sheet joins `e₂`. -/
noncomputable def secondMergeInput (shape : Shape profile) : MergeInput profile where
  own := profile.second
  other := profile.first
  own_target := profile.second_target
  other_target := profile.first_target
  own_survives := profile.second_survives
  other_survives := profile.first_survives
  own_extra := second_extra_separate shape
  other_extra := first_extra_separate shape
  separate := fun h ↦ first_second_separate profile h.symm
  covers := fun sheet hSheet ↦ by
    rcases endpointPartition_covers shape sheet hSheet with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  star_eq := incoming_star_swap

theorem firstMergeInput_member (shape : Shape profile) :
    (firstMergeInput shape).member = firstShape shape := rfl

theorem secondMergeInput_member (shape : Shape profile) :
    (secondMergeInput shape).member = secondShape shape := rfl

/-- **Figure 35's `M⁽¹⁾`, as the core's graph data.** -/
noncomputable def firstGraphData (shape : Shape profile) (input : W2SourceInput data star) :
    GraphData data wall :=
  mergeGraphData shape input (firstMergeInput shape) (firstCensus shape input)

/-- **Figure 35's `M⁽²⁾`, as the core's graph data.** -/
noncomputable def secondGraphData (shape : Shape profile) (input : W2SourceInput data star) :
    GraphData data wall :=
  mergeGraphData shape input (secondMergeInput shape) (secondCensus shape input)

@[simp] theorem firstGraphData_toSelectedData (shape : Shape profile)
    (input : W2SourceInput data star) :
    (firstGraphData shape input).toSelectedData = selectedData input (firstCensus shape input) :=
  rfl

@[simp] theorem secondGraphData_toSelectedData (shape : Shape profile)
    (input : W2SourceInput data star) :
    (secondGraphData shape input).toSelectedData =
      selectedData input (secondCensus shape input) := rfl

/-! ## §5  `M⁽³⁾`: the branch vertex is the `t₂` endpoint above `A₀ ∖ {x}` -/

namespace Third

variable (shape : Shape profile)

/-- `e₂`'s sheet lies in `M⁽³⁾`'s big `t₂` block. -/
theorem fine_second : (thirdShape shape).fine.Rel (firstSheet profile) (secondSheet profile) :=
  (thirdFine_rel_iff shape (secondSheet profile)).mpr
    ⟨secondSheet_rel profile, fun h ↦ extra_ne_second shape h.symm⟩

/-- The big `t₂` block carries exactly the two `t₂` survivors. -/
theorem endpoint_blockCountWithin :
    (endpointPartition profile).blockCountWithin (thirdShape shape).fine
      (firstSheet profile) = 2 := by
  refine blockCountWithin_eq_two _ _ (firstSheet profile) (secondSheet profile)
    (firstSheet profile) rfl (fine_second shape) ?_ (first_second_separate profile)
  intro sheet hSheet
  have hData := (thirdFine_rel_iff shape sheet).mp hSheet
  rcases endpointPartition_covers shape sheet hData.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (Finset.mem_singleton.mp (by
      rw [← extraSheet_block shape]
      exact (SheetPartition.mem_block_iff _ _ _).mpr h)) hData.2

/-- **The branch `t₂` endpoint is trivalent**: `e₁`, `e₂` and the regrown
occurrence. -/
theorem old_card :
    Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile))) = 3 := by
  rw [(thirdShape shape).card_incident_old_selected (firstSheet profile)
    (firstSheet_rel profile), endpoint_blockCountWithin shape]

/-- The dangling singleton's `t₂` endpoint is divalent -- and in fact entirely
pruned. -/
theorem extra_card :
    Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (extraSheet profile))) = 2 := by
  rw [(thirdShape shape).card_incident_old_selected (extraSheet profile)
    (extraSheet_rel profile)]
  exact congrArg (1 + ·) (SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
    ((data.vertexPartition wall).detachSheet_block_single (extraSheet profile)
      (firstSheet profile) (extra_ne_first shape) (wall_extra_first profile)))

/-- **The `t₃` endpoint above `A₀` is trivalent**, its third incidence being
the pruned regrown occurrence of the dangling singleton. -/
theorem fresh_card (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Fintype.card (IncidentSourceEdge (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) anchor)) = 3 := by
  rw [(thirdShape shape).card_incident_fresh_selected shape anchor hAnchor]
  exact congrArg (· + 1) (thirdMember_blockCountWithin shape anchor hAnchor).2.1

theorem new_first_ne_extra :
    (thirdShape shape).candidate.newSourceEdge (firstSheet profile) ≠
      (thirdShape shape).candidate.newSourceEdge (extraSheet profile) := fun h ↦
  thirdShape_fine_not_rel shape
    (((thirdShape shape).newSourceEdge_eq_iff_fine (firstSheet profile) (extraSheet profile)
      (firstSheet_rel profile)).mp h)

theorem old_first_ne_second :
    (thirdShape shape).candidate.oldSourceEdge profile.first.1 ≠
      (thirdShape shape).candidate.oldSourceEdge profile.second.1 := fun h ↦
  profile.first_ne_second (Subtype.ext (ResolutionCut.oldSourceEdge_injective _ h))

theorem first_incident :
    Incident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.oldSourceEdge profile.first.1)
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile)) :=
  (thirdShape shape).double_incident_fine profile.first.1 profile.first_target
    (firstSheet profile) (firstSheet_rel profile) rfl

theorem second_incident :
    Incident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.oldSourceEdge profile.second.1)
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile)) :=
  (thirdShape shape).double_incident_fine profile.second.1 profile.second_target
    (firstSheet profile) (firstSheet_rel profile) (fine_second shape)

theorem third_incident (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Incident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.oldSourceEdge profile.third.1)
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) anchor) :=
  (thirdShape shape).single_incident profile.third.1 profile.third_target anchor
    (hAnchor.symm.trans third_sheet_rel)

theorem new_extra_incident_fresh (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Incident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (extraSheet profile))
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
  rw [← (thirdShape shape).sourceEndpoint_fresh_eq_of_rel (extraSheet profile) anchor
    ((extraSheet_rel profile).symm.trans hAnchor)]
  exact LimitChainCore.newSourceEdge_incident_fresh (candidate := (thirdShape shape).candidate) _

theorem new_first_incident_fresh (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Incident (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.newSourceEdge (firstSheet profile))
      ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
  rw [← (thirdShape shape).sourceEndpoint_fresh_eq_of_rel (firstSheet profile) anchor
    ((firstSheet_rel profile).symm.trans hAnchor)]
  exact LimitChainCore.newSourceEdge_incident_fresh (candidate := (thirdShape shape).candidate) _

/-- **`M⁽³⁾`'s branch star.**  `e₁`, `e₂` retained and the surviving regrown
occurrence. -/
theorem old_star (input : W2SourceInput data star) :
    nonDanglingIncident (thirdShape shape).candidate.datum
        ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
          (firstSheet profile)) =
      {(thirdShape shape).candidate.oldSourceEdge profile.first.1,
        (thirdShape shape).candidate.oldSourceEdge profile.second.1,
        (thirdShape shape).candidate.newSourceEdge (firstSheet profile)} :=
  LimitChainCore.nonDanglingIncident_triple_of_card_three _ (first_incident shape)
    (second_incident shape)
    (LimitChainCore.newSourceEdge_incident_old
      (candidate := (thirdShape shape).candidate) (firstSheet profile))
    (old_first_ne_second shape) (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    ((thirdShape shape).retained_survives input ⟨profile.first.1, profile.first_survives⟩)
    ((thirdShape shape).retained_survives input ⟨profile.second.1, profile.second_survives⟩)
    (thirdShape_new_first_survives shape input) (old_card shape)

/-- **The `t₃` endpoint above `A₀` is divalent**: the surviving regrown
occurrence and `e₃`. -/
theorem fresh_star (input : W2SourceInput data star) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingIncident (thirdShape shape).candidate.datum
        ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) anchor) =
      {(thirdShape shape).candidate.newSourceEdge (firstSheet profile),
        (thirdShape shape).candidate.oldSourceEdge profile.third.1} :=
  LimitChainCore.nonDanglingIncident_pair_of_card_three _
    (new_first_incident_fresh shape anchor hAnchor) (third_incident shape anchor hAnchor)
    (new_extra_incident_fresh shape anchor hAnchor)
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm
    (new_first_ne_extra shape)
    (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)
    (thirdShape_new_first_survives shape input)
    ((thirdShape shape).retained_survives input ⟨profile.third.1, profile.third_survives⟩)
    (thirdShape_new_extra_dangles shape input) (fresh_card shape anchor hAnchor)

/-- The surviving regrown occurrence joins `e₃`'s row, through the divalent
`t₃` endpoint whose third incidence is the pruned regrown singleton. -/
theorem new_first_row (input : W2SourceInput data star) :
    NonDanglingEdge.stablePath
        (⟨(thirdShape shape).candidate.newSourceEdge (firstSheet profile),
          thirdShape_new_first_survives shape input⟩ :
          NonDanglingEdge (thirdShape shape).candidate.datum) =
      (retainedEdge (thirdShape shape).candidate input.valid.1
        ⟨profile.third.1, profile.third_survives⟩).stablePath :=
  (thirdShape shape).trivalent_stablePath input _ _
    (new_first_incident_fresh shape (firstSheet profile) (firstSheet_rel profile))
    (third_incident shape (firstSheet profile) (firstSheet_rel profile)) _
    (new_extra_incident_fresh shape (firstSheet profile) (firstSheet_rel profile))
    (thirdShape_new_extra_dangles shape input)
    (fresh_card shape (firstSheet profile) (firstSheet_rel profile))

/-- The incoming surviving star, read at `M⁽³⁾`'s anchor. -/
theorem incoming_star_at :
    nonDanglingIncident data (data.sourceEndpoint wall (firstSheet profile)) =
      {profile.first.1, profile.second.1, profile.third.1} := by
  rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall (firstSheet_rel profile)]
  exact incoming_star

/-- **The branch flag really is the branch star.** -/
theorem flag_image (input : W2SourceInput data star) :
    (nonDanglingIncident data (data.sourceEndpoint wall (firstSheet profile))).image
        (singleFlag (thirdShape shape) (firstSheet profile)) =
      nonDanglingIncident (thirdShape shape).candidate.datum
        ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
          (firstSheet profile)) := by
  rw [old_star shape input, incoming_star_at, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton,
    singleFlag_double (thirdShape shape) (firstSheet profile) profile.first_target,
    singleFlag_double (thirdShape shape) (firstSheet profile) profile.second_target,
    singleFlag_single (thirdShape shape) (firstSheet profile) profile.third_target]

theorem old_valency (input : W2SourceInput data star) :
    nonDanglingValency (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile)) = 3 := by
  classical
  rw [← card_nonDanglingIncident, old_star shape input,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨old_first_ne_second shape, LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _⟩),
    Finset.card_pair (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _)]

theorem flag_injOn (input : W2SourceInput data star) :
    Set.InjOn (singleFlag (thirdShape shape) (firstSheet profile))
      ↑(nonDanglingIncident data (data.sourceEndpoint wall (firstSheet profile))) := by
  classical
  have hIncoming : nonDanglingValency data (data.sourceEndpoint wall (firstSheet profile)) = 3 := by
    rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall (firstSheet_rel profile)]
    exact profile.valency
  apply Finset.injOn_of_card_image_eq
  rw [flag_image shape input, card_nonDanglingIncident, card_nonDanglingIncident,
    old_valency shape input, hIncoming]

theorem flag_row (input : W2SourceInput data star) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall (firstSheet profile)))
    (hFlag : ¬ IsDangling (thirdShape shape).candidate.datum
      (singleFlag (thirdShape shape) (firstSheet profile) edge)) :
    NonDanglingEdge.stablePath
        (⟨singleFlag (thirdShape shape) (firstSheet profile) edge, hFlag⟩ :
          NonDanglingEdge (thirdShape shape).candidate.datum) =
      (retainedEdge (thirdShape shape).candidate input.valid.1 ⟨edge, hSurvives⟩).stablePath := by
  have hMem : edge ∈ nonDanglingIncident data (data.sourceEndpoint wall (firstSheet profile)) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvives, hIncident⟩
  rw [incoming_star_at] at hMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl | rfl
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (singleFlag_double (thirdShape shape) (firstSheet profile)
        profile.first_target))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (singleFlag_double (thirdShape shape) (firstSheet profile)
        profile.second_target))
  · exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (singleFlag_single (thirdShape shape) (firstSheet profile)
        profile.third_target))) (new_first_row shape input)

/-- **Every other expanded endpoint above `A₀` is divalent or pruned.** -/
theorem not_branch (input : W2SourceInput data star) (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel (firstSheet profile) sheet)
    (hNe : (thirdShape shape).candidate.datum.sourceEndpoint
        (wallSide target wall side) sheet ≠
      (thirdShape shape).candidate.datum.sourceEndpoint (wallSide target wall false)
        (firstSheet profile)) :
    nonDanglingValency (thirdShape shape).candidate.datum
      ((thirdShape shape).candidate.datum.sourceEndpoint
        (wallSide target wall side) sheet) ≤ 2 := by
  classical
  have hWall : (data.vertexPartition wall).Rel block.1 sheet :=
    (firstSheet_rel profile).trans hSheet
  cases side with
  | false =>
      show nonDanglingValency (thirdShape shape).candidate.datum
        ((thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2
      rcases thirdShape_fine_cover shape sheet hWall with h | h
      · exact absurd ((thirdShape shape).sourceEndpoint_old_eq_of_fine (firstSheet profile)
          sheet (firstSheet_rel profile) h).symm hNe
      · rw [← (thirdShape shape).sourceEndpoint_old_eq_of_fine (extraSheet profile) sheet
          (extraSheet_rel profile) h]
        refine le_of_le_of_eq
          (NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge _ _) ?_
        exact extra_card shape
  | true =>
      show nonDanglingValency (thirdShape shape).candidate.datum
        ((thirdShape shape).candidate.datum.sourceEndpoint (freshVertex target) sheet) ≤ 2
      rw [← card_nonDanglingIncident, fresh_star shape input sheet hWall,
        Finset.card_pair (LimitChainCore.oldSourceEdge_ne_newSourceEdge _ _).symm]

end Third

/-- **Figure 35's `M⁽³⁾` (in the genus-preserving form of
`W2PSourceCandidates`), as the core's graph data.**  Its branch
vertex is the `t₂` endpoint above `A₀ ∖ {x}` (`selectedSide = false`), so the
bundle is re-anchored there: the wall block's canonical representative may be
the dangling sheet itself, whose `t₂` endpoint is entirely pruned. -/
noncomputable def thirdGraphData (shape : Shape profile) (input : W2SourceInput data star) :
    GraphData data wall where
  toSelectedData := reanchor (selectedData input (thirdCensus shape input))
    (firstSheet profile) (firstSheet_rel profile)
  selectedSide := false
  selectedFlag := singleFlag (thirdShape shape) (firstSheet profile)
  selectedFlag_star := (Third.flag_image shape input).symm
  selectedFlag_injOn := Third.flag_injOn shape input
  selected_not_branch := Third.not_branch shape input
  selectedFlag_row := Third.flag_row shape input

@[simp] theorem thirdGraphData_candidate (shape : Shape profile)
    (input : W2SourceInput data star) :
    (thirdGraphData shape input).candidate = (thirdShape shape).candidate := rfl

/-! ## §6  The stable incidence graph of each Figure 35 member

`LimitChainCore.GraphData.equivalence` is a bijection of surviving branch
vertices together with the occurrence-induced row bijection, preserving
`incidenceCount` at every branch/row pair.  Its row map is literally
`W2PRowDescent.stablePathEquiv` -- for `M⁽³⁾` too, because re-anchoring leaves
the retained-occurrence lift alone -- so the stable incidence dictionary and
the limit matrices of `W2PLimitMatrix` speak about the same rows. -/

/-- **`M⁽¹⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def firstEquivalence (shape : Shape profile) (input : W2SourceInput data star) :
    StableGraphIncidence.Equivalence data (firstShape shape).candidate.datum :=
  (firstGraphData shape input).equivalence

/-- **`M⁽²⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def secondEquivalence (shape : Shape profile) (input : W2SourceInput data star) :
    StableGraphIncidence.Equivalence data (secondShape shape).candidate.datum :=
  (secondGraphData shape input).equivalence

/-- **`M⁽³⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def thirdEquivalence (shape : Shape profile) (input : W2SourceInput data star) :
    StableGraphIncidence.Equivalence data (thirdShape shape).candidate.datum :=
  (thirdGraphData shape input).equivalence

@[simp] theorem firstEquivalence_row (shape : Shape profile)
    (input : W2SourceInput data star) :
    (firstEquivalence shape input).row = stablePathEquiv input (firstCensus shape input) := rfl

@[simp] theorem secondEquivalence_row (shape : Shape profile)
    (input : W2SourceInput data star) :
    (secondEquivalence shape input).row = stablePathEquiv input (secondCensus shape input) := rfl

@[simp] theorem thirdEquivalence_row (shape : Shape profile)
    (input : W2SourceInput data star) :
    (thirdEquivalence shape input).row = stablePathEquiv input (thirdCensus shape input) := rfl

/-- Path ends transport to `M⁽¹⁾`. -/
theorem firstHasPathEnds (shape : Shape profile) (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) : HasPathEnds (firstShape shape).candidate.datum :=
  (firstGraphData shape input).hasPathEnds hEnds

/-- Path ends transport to `M⁽²⁾`. -/
theorem secondHasPathEnds (shape : Shape profile) (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) : HasPathEnds (secondShape shape).candidate.datum :=
  (secondGraphData shape input).hasPathEnds hEnds

/-- Path ends transport to `M⁽³⁾`. -/
theorem thirdHasPathEnds (shape : Shape profile) (input : W2SourceInput data star)
    (hEnds : HasPathEnds data) : HasPathEnds (thirdShape shape).candidate.datum :=
  (thirdGraphData shape input).hasPathEnds hEnds

/-! ## §7  Which expanded endpoint is each member's branch vertex

`LimitChainCore.GraphData.branchVertex` is the endpoint above the bundle's own
anchor on the side `selectedSide` names.  These four identities are the
statement of the case analysis this module carries out. -/

@[simp] theorem firstGraphData_selectedSide (shape : Shape profile)
    (input : W2SourceInput data star) :
    (firstGraphData shape input).selectedSide = true := rfl

@[simp] theorem secondGraphData_selectedSide (shape : Shape profile)
    (input : W2SourceInput data star) :
    (secondGraphData shape input).selectedSide = true := rfl

@[simp] theorem thirdGraphData_selectedSide (shape : Shape profile)
    (input : W2SourceInput data star) :
    (thirdGraphData shape input).selectedSide = false := rfl

/-- **`M⁽¹⁾`'s branch vertex is the `t₃` endpoint above `A₀`.** -/
theorem firstGraphData_branchVertex (shape : Shape profile)
    (input : W2SourceInput data star) :
    (firstGraphData shape input).branchVertex =
      (firstShape shape).candidate.datum.sourceEndpoint (freshVertex target) block.1 := rfl

/-- **`M⁽²⁾`'s branch vertex is the `t₃` endpoint above `A₀`.** -/
theorem secondGraphData_branchVertex (shape : Shape profile)
    (input : W2SourceInput data star) :
    (secondGraphData shape input).branchVertex =
      (secondShape shape).candidate.datum.sourceEndpoint (freshVertex target) block.1 := rfl

/-- **`M⁽³⁾`'s branch vertex is the `t₂` endpoint above `A₀ ∖ {x}`.** -/
theorem thirdGraphData_branchVertex (shape : Shape profile)
    (input : W2SourceInput data star) :
    (thirdGraphData shape input).branchVertex =
      (thirdShape shape).candidate.datum.sourceEndpoint (oldVertex target wall)
        (firstSheet profile) := rfl

/-- **`M⁽¹⁾`'s branch star**, read off the census: the two regrown occurrences
and `e₃`. -/
theorem firstGraphData_branchVertex_star (shape : Shape profile)
    (input : W2SourceInput data star) :
    nonDanglingIncident (firstShape shape).candidate.datum
        (firstGraphData shape input).branchVertex =
      {(firstShape shape).candidate.newSourceEdge (firstSheet profile),
        (firstShape shape).candidate.newSourceEdge (secondSheet profile),
        (firstShape shape).candidate.oldSourceEdge profile.third.1} :=
  (firstMergeInput shape).fresh_star shape input block.1 rfl

/-- **`M⁽²⁾`'s branch star.** -/
theorem secondGraphData_branchVertex_star (shape : Shape profile)
    (input : W2SourceInput data star) :
    nonDanglingIncident (secondShape shape).candidate.datum
        (secondGraphData shape input).branchVertex =
      {(secondShape shape).candidate.newSourceEdge (secondSheet profile),
        (secondShape shape).candidate.newSourceEdge (firstSheet profile),
        (secondShape shape).candidate.oldSourceEdge profile.third.1} :=
  (secondMergeInput shape).fresh_star shape input block.1 rfl

/-- **`M⁽³⁾`'s branch star**: `e₁`, `e₂` retained and the surviving regrown
occurrence. -/
theorem thirdGraphData_branchVertex_star (shape : Shape profile)
    (input : W2SourceInput data star) :
    nonDanglingIncident (thirdShape shape).candidate.datum
        (thirdGraphData shape input).branchVertex =
      {(thirdShape shape).candidate.oldSourceEdge profile.first.1,
        (thirdShape shape).candidate.oldSourceEdge profile.second.1,
        (thirdShape shape).candidate.newSourceEdge (firstSheet profile)} :=
  Third.old_star shape input

end DraismaVargas.LocalCases.W2PGraphData
