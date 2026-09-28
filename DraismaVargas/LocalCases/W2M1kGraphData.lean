import DraismaVargas.LocalCases.W2M1kRowDescent

/-!
# Figure 33's stable incidence graph, for the two divalent members

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w2-r2-nd3-M-1k}` and its Figure 33.

`W2M1kStableLift` reads Figure 33's two divalent members as the core's
`LimitChainCore.SelectedData` and `W2M1kRowDescent` turns that into each
member's geometric stable-row bijection.  The certified exit also needs the
**branch half**: a flag dictionary at the member's own branch vertex
above the distinguished block `A₀`, which is the core's
`LimitChainCore.GraphData`, and with it `LimitChainCore.GraphData.equivalence`
-- the member's stable incidence graph identified with the incoming one.

This is the M-1k analogue of `W2MkkGraphData`, and the M-1k geometry makes it
shorter: no re-anchoring is needed (see below), and each member's branch star
is a single named census identity.

## Where each member's branch vertex sits

Above `A₀` the incoming source vertex is trivalent, carrying `e₁`, `e₂` (both
above `t₂ = doubleLabel`) and `e₃` (above `t₃ = singleLabel`); Cardinality M
puts the dangling `e₄` above `t₃` as well
(`W2M1kSourceCandidates.Shape.deleted_single`).  Which of the two-star's two
labels is `t₂` is **not** fixed by the bundle, so every statement below names a
side as `W2M1kStableGraph.sideOf profile.doubleLabel` or
`W2M1kStableGraph.sideOf profile.singleLabel`, never as `old`/`fresh`.  The
flag dictionary is read off `W2M1kStableGraph`'s census, never off a
cardinality:

* `M⁽²⁾` (`DividedData.candidate`, Base II.2.2.M).  Its two `t₂` endpoints are
  divalent: over `e₁`'s sheet it carries `e₁` and the regrown singleton
  (`divided_nonDanglingValency_unit`), over the rest of `A₀` it carries `e₂`
  and the residual regrown occurrence, the third incidence having died with
  `e₄` (`divided_nonDanglingValency_pair`,
  `W2M1kStableGraph.divided_new_deleted_dangling`).  Its `t₃` endpoint over
  `{e₄'s sheet}` is entirely pruned (`divided_nonDanglingValency_deleted`), and
  its `t₃` endpoint over `A₀ ∖ {e₄'s sheet}` carries the retained `e₃` and both
  surviving regrown occurrences: the **branch vertex**
  (`divided_nonDanglingIncident_branch`).  So `selectedSide` is
  `sideOf profile.singleLabel`, and the flag retains `e₃`, sends `e₁` to the
  regrown singleton over its own sheet and `e₂` to the residual one.
* `M⁽³⁾` (`joinedCandidate`, Base II.1.M).  Its `t₃` endpoint is divalent,
  joining the one regrown occurrence to `e₃`
  (`joined_nonDanglingValency_single`), and its `t₂` endpoint over the whole of
  `A₀` carries `e₁`, `e₂` and that regrown occurrence
  (`joined_nonDanglingIncident_double`): the **branch vertex**.  So
  `selectedSide` is `sideOf profile.doubleLabel` -- the **opposite** side from
  `M⁽²⁾`'s -- and the flag retains `e₁` and `e₂` and sends `e₃` to the regrown
  occurrence.

## No re-anchoring

`LimitChainCore.GraphData` reads the branch vertex above the expanded endpoint
of the bundle's own anchor `selected`.  `W2MkkGraphData` needs
`W2MkkGraphData.reanchor` because `W2MkkStableLift` anchors every member at
the wall block's canonical representative `block.1`, which a detaching member
may separate off.  `W2M1kStableLift` chooses its anchors so that no
re-anchoring is needed here: `M⁽³⁾` keeps the whole block at both endpoints and
is anchored at
`block.1`; `M⁽²⁾` is anchored at `pinSheet profile profile.doubleLabel`, which
`W2M1kStableGraph.divided_pin_ne` separates from the pruned singleton
`pinSheet profile profile.singleLabel`, so the branch vertex above the anchor
is the surviving trivalent one.  Nothing below re-anchors, and the two members'
`SelectedData` -- hence every `W2M1kLimitMatrix` evaluation and every
`W2M1kRowDescent` bijection -- is used exactly as it was built.

## Discipline

Every endpoint statement below is an identity of **occurrence** sets read off
`W2M1kStableGraph`'s exported census; no stable row is asserted distinct from
another, so a stable loop through a branch vertex is not excluded, and no
cardinality argument replaces the census anywhere.  Injectivity of a flag is
proved from named occurrence-distinctness facts
(`W2M1kStableGraph.divided_newSourceEdge_pin_ne`,
`LimitChainCore.oldSourceEdge_ne_newSourceEdge`,
`ResolutionCut.oldSourceEdge_injective`), never from a count.

## The leaf member `M⁽¹⁾` is not here

`W2M1kStableLift.leaf_not_wallCandidate` is a theorem: Base I.a's retained
endpoint is a target leaf and carries no wall direction, so `M⁽¹⁾` has no
`LimitChainCore.WallCandidate`, hence no `SelectedData` and no `GraphData`.
Its branch dictionary is a bespoke construction on the `M11Split*` pattern and
is not attempted here; see `W2M1kStableIncidence` §6 for exactly what it must
supply.

Member 2 of `W2M1kSwapped.SwappedBundle.candidates` is not transported here
either: it is obtained by instantiating the divided definitions below at
`W2M1kSwapped.swappedData` with a transported `W2SourceInput`, `SourceProfile`,
`Shape` and `DividedData`, exactly as `W2M1kStableLift` records.
-/

namespace DraismaVargas.LocalCases.W2M1kGraphData

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates
open W2M1kStableGraph W2M1kStableLift W2M1kRowDescent
open LimitChainCore (SelectedData GraphData wallSide oldSourceEdge_ne_newSourceEdge
  sourceEndpoint_eq_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The incoming surviving star above `A₀`

The profile's four occurrences exhaust the distinguished vertex's star and the
fourth one dangles, so the surviving star is the displayed triple.  Nothing in
this section is special to M-1k. -/

/-- **The distinguished source vertex carries exactly `e₁`, `e₂`, `e₃`.** -/
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

/-- `e₁` and `e₂` are distinct occurrences. -/
theorem first_ne_second_edge
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first.1 ≠ profile.second.1 :=
  fun hEqual ↦ profile.first_ne_second (Subtype.ext hEqual)

/-- `e₃` is not above `t₂`. -/
theorem third_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.third.1.1.1 ≠ star.edge profile.doubleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (hTarget.symm.trans profile.third_target))

/-- `e₁` is not above `t₃`. -/
theorem first_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first.1.1.1 ≠ star.edge profile.singleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (profile.first_target.symm.trans hTarget))

/-- `e₂` is not above `t₃`. -/
theorem second_target_ne (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.second.1.1.1 ≠ star.edge profile.singleLabel := fun hTarget ↦
  profile.labels_ne (star.edge_injective (profile.second_target.symm.trans hTarget))

/-- `e₁`'s sheet is the `t₂` pinned sheet: that is what `Shape.unit_index`
says. -/
theorem first_sheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.first.1.1.2 = pinSheet profile profile.doubleLabel :=
  (congrArg (fun edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block) ↦
    edge.1.1.2) (pinnedOccurrence_double (profile := profile))).symm

/-- `e₂`'s sheet is the `t₂` bulk sheet. -/
theorem second_sheet (profile : W2R2SourceProfile.SourceProfile data star block) :
    profile.second.1.1.2 = bulkSheet profile profile.doubleLabel :=
  (congrArg (fun edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block) ↦
    edge.1.1.2) (bulkOccurrence_double (profile := profile))).symm

/-- The anchor is related to itself. -/
theorem block_rel_self (data : GluingDatum target degree) (wall : target.V)
    (block : WallBlock data wall) :
    (data.vertexPartition wall).Rel block.1 block.1 :=
  ((data.vertexPartition wall).rel_iff _ _).mpr rfl

/-! ## §2  `M⁽²⁾`'s branch flag

Its branch vertex is the `t₃` endpoint over `A₀ ∖ {e₄'s sheet}`, above the
anchor `pinSheet profile profile.doubleLabel`.  The flag retains `e₃` and sends
a `t₂` occurrence to the regrown occurrence of its own sheet's class: the
pinned singleton for `e₁`, the residual class for everything else. -/

/-- The sheet naming the regrown partner of a `t₂` occurrence: its own sheet
when that is `e₁`'s, the residual sheet otherwise. -/
noncomputable def dividedSheet (divided : DividedData profile) (sheet : Fin degree) :
    Fin degree :=
  if sheet = pinSheet profile profile.doubleLabel then pinSheet profile profile.doubleLabel
  else divided.third

@[simp] theorem dividedSheet_pin (divided : DividedData profile) :
    dividedSheet divided (pinSheet profile profile.doubleLabel) =
      pinSheet profile profile.doubleLabel := if_pos rfl

theorem dividedSheet_of_ne (divided : DividedData profile) {sheet : Fin degree}
    (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    dividedSheet divided sheet = divided.third := if_neg hNe

/-- **The branch flag of `M⁽²⁾`.** -/
noncomputable def dividedFlag (shape : Shape profile) (divided : DividedData profile)
    (edge : data.SourceEdge) : (DividedData.candidate shape divided).datum.SourceEdge :=
  if edge.1.1 = star.edge profile.doubleLabel then
    (DividedData.candidate shape divided).newSourceEdge (dividedSheet divided edge.1.2)
  else (DividedData.candidate shape divided).oldSourceEdge edge

theorem dividedFlag_double (shape : Shape profile) (divided : DividedData profile)
    {edge : data.SourceEdge} (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    dividedFlag shape divided edge =
      (DividedData.candidate shape divided).newSourceEdge
        (dividedSheet divided edge.1.2) := if_pos hTarget

theorem dividedFlag_not_double (shape : Shape profile) (divided : DividedData profile)
    {edge : data.SourceEdge} (hTarget : ¬ edge.1.1 = star.edge profile.doubleLabel) :
    dividedFlag shape divided edge =
      (DividedData.candidate shape divided).oldSourceEdge edge := if_neg hTarget

/-- `e₁` goes to the regrown singleton over its own sheet. -/
theorem dividedFlag_first (shape : Shape profile) (divided : DividedData profile) :
    dividedFlag shape divided profile.first.1 =
      (DividedData.candidate shape divided).newSourceEdge
        (pinSheet profile profile.doubleLabel) := by
  rw [dividedFlag_double shape divided profile.first_target, first_sheet profile,
    dividedSheet_pin]

/-- `e₂` goes to the residual regrown occurrence. -/
theorem dividedFlag_second (shape : Shape profile) (divided : DividedData profile) :
    dividedFlag shape divided profile.second.1 =
      (DividedData.candidate shape divided).newSourceEdge divided.third := by
  rw [dividedFlag_double shape divided profile.second_target, second_sheet profile,
    dividedSheet_of_ne divided (bulkSheet_ne_pinSheet shape profile.doubleLabel)]

/-- `e₃` is retained. -/
theorem dividedFlag_third (shape : Shape profile) (divided : DividedData profile) :
    dividedFlag shape divided profile.third.1 =
      (DividedData.candidate shape divided).oldSourceEdge profile.third.1 :=
  dividedFlag_not_double shape divided (third_target_ne profile)

/-- **The three images are pairwise distinct.**  The two regrown ones because
`e₁`'s sheet is a singleton block of the member's new edge
(`divided_newSourceEdge_pin_ne`), the retained one because a retained
occurrence is never a regrown one. -/
theorem divided_flag_distinct (shape : Shape profile) (divided : DividedData profile) :
    dividedFlag shape divided profile.first.1 ≠ dividedFlag shape divided profile.second.1 ∧
      dividedFlag shape divided profile.first.1 ≠ dividedFlag shape divided profile.third.1 ∧
      dividedFlag shape divided profile.second.1 ≠
        dividedFlag shape divided profile.third.1 := by
  have hFirst := dividedFlag_first shape divided
  have hSecond := dividedFlag_second shape divided
  have hThird := dividedFlag_third shape divided
  refine ⟨?_, ?_, ?_⟩
  · rw [hFirst, hSecond]
    exact divided_newSourceEdge_pin_ne shape divided profile.doubleLabel divided.third
      (divided_third_ne_pin divided profile.doubleLabel)
  · rw [hFirst, hThird]
    exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)
  · rw [hSecond, hThird]
    exact Ne.symm (oldSourceEdge_ne_newSourceEdge _ _)

/-! ### The four `GraphData` fields at `M⁽²⁾`'s branch vertex -/

/-- **The flag dictionary at the branch vertex.**  Read off
`divided_nonDanglingIncident_branch` and the incoming star, not off a
cardinality. -/
theorem divided_selectedFlag_star (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    nonDanglingIncident (DividedData.candidate shape divided).datum
        ((DividedData.candidate shape divided).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.singleLabel))
          (pinSheet profile profile.doubleLabel)) =
      (nonDanglingIncident data
        (data.sourceEndpoint wall (pinSheet profile profile.doubleLabel))).image
          (dividedFlag shape divided) := by
  classical
  rw [divided_nonDanglingIncident_branch input shape divided
      (pinSheet profile profile.doubleLabel) (pin_rel_pin profile 0 profile.doubleLabel)
      (divided_pin_ne divided profile.labels_ne),
    incoming_star_at profile (pinSheet_rel profile.doubleLabel)]
  simp only [Finset.image_insert, Finset.image_singleton, dividedFlag_first,
    dividedFlag_second, dividedFlag_third]
  ext edge
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem divided_selectedFlag_injOn (shape : Shape profile) (divided : DividedData profile) :
    Set.InjOn (dividedFlag shape divided)
      ↑(nonDanglingIncident data
        (data.sourceEndpoint wall (pinSheet profile profile.doubleLabel))) := by
  classical
  obtain ⟨h12, h13, h23⟩ := divided_flag_distinct shape divided
  rw [incoming_star_at profile (pinSheet_rel profile.doubleLabel)]
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
pruned.**  The two `t₂` endpoints are divalent, the `t₃` endpoint over `{e₄'s
sheet}` is empty, and every other `t₃` endpoint above `A₀` *is* the branch
vertex. -/
theorem divided_selected_not_branch (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (side : Bool) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel (pinSheet profile profile.doubleLabel) sheet)
    (hNotBranch : (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet ≠
      (DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.singleLabel))
        (pinSheet profile profile.doubleLabel)) :
    nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet) ≤ 2 := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet :=
    (pin_rel_pin profile 0 profile.doubleLabel).trans hRel
  rcases Shape.label_cases profile (sideLabel side) with hLabel | hLabel
  · have hSide : side = sideOf profile.doubleLabel := side_eq_sideOf hLabel
    subst hSide
    by_cases hPin : sheet = pinSheet profile profile.doubleLabel
    · subst hPin
      have := divided_nonDanglingValency_unit input shape divided
      omega
    · have := divided_nonDanglingValency_pair input shape divided sheet hWall hPin
      omega
  · have hSide : side = sideOf profile.singleLabel := side_eq_sideOf hLabel
    subst hSide
    by_cases hPin : sheet = pinSheet profile profile.singleLabel
    · subst hPin
      have := divided_nonDanglingValency_deleted input shape divided
      omega
    · exact absurd (divided_single_endpoint_eq shape divided sheet
        (pinSheet profile profile.doubleLabel) hWall hPin
        (pin_rel_pin profile 0 profile.doubleLabel)
        (divided_pin_ne divided profile.labels_ne)) hNotBranch

/-- **The flag preserves stable rows.**  A retained `e₃` keeps its own row;
`e₁` and the regrown singleton are consecutive at the divalent `t₂` endpoint
over `e₁`'s sheet (`divided_new_unit_stablePath_eq`), and `e₂` and the residual
regrown occurrence at the other `t₂` endpoint
(`divided_new_third_stablePath_eq`). -/
theorem divided_selectedFlag_row (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge
      (data.sourceEndpoint wall (pinSheet profile profile.doubleLabel)))
    (hFlag : ¬ IsDangling (DividedData.candidate shape divided).datum
      (dividedFlag shape divided edge)) :
    NonDanglingEdge.stablePath (⟨dividedFlag shape divided edge, hFlag⟩ :
        NonDanglingEdge (DividedData.candidate shape divided).datum) =
      (retainedEdge (DividedData.candidate shape divided) input.valid.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge data)).stablePath := by
  classical
  by_cases hTarget : edge.1.1 = star.edge profile.doubleLabel
  · have hMem : edge ∈ nonDanglingIncident data
        (data.sourceEndpoint wall (pinSheet profile profile.doubleLabel)) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvives, hIncident⟩
    rw [incoming_star_at profile (pinSheet_rel profile.doubleLabel)] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact Eq.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext (dividedFlag_first shape divided)))
        (divided_new_unit_stablePath_eq input shape divided)
    · exact Eq.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext (dividedFlag_second shape divided)))
        (divided_new_third_stablePath_eq input shape divided)
    · exact absurd hTarget (third_target_ne profile)
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (dividedFlag_not_double shape divided hTarget))

/-- **Figure 33's `M⁽²⁾` as the core's `GraphData`.**  `selectedSide` is
`sideOf profile.singleLabel`: its branch vertex is the `t₃` endpoint over
`A₀ ∖ {e₄'s sheet}`, of surviving valency three. -/
noncomputable def dividedGraphData (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) : GraphData data wall where
  toSelectedData := dividedSelectedData input shape divided
  selectedSide := sideOf profile.singleLabel
  selectedFlag := dividedFlag shape divided
  selectedFlag_star := divided_selectedFlag_star input shape divided
  selectedFlag_injOn := divided_selectedFlag_injOn shape divided
  selected_not_branch := divided_selected_not_branch input shape divided
  selectedFlag_row := divided_selectedFlag_row input shape divided

@[simp] theorem dividedGraphData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedGraphData input shape divided).candidate =
      DividedData.candidate shape divided := rfl

@[simp] theorem dividedGraphData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedGraphData input shape divided).selected =
      pinSheet profile profile.doubleLabel := rfl

@[simp] theorem dividedGraphData_selectedSide (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedGraphData input shape divided).selectedSide = sideOf profile.singleLabel := rfl

/-- The row half is untouched: the member's stable-row bijection is still
`W2M1kRowDescent.dividedStablePathEquiv`. -/
theorem dividedGraphData_stablePathEquiv (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedGraphData input shape divided).stablePathEquiv =
      dividedStablePathEquiv input shape divided := rfl

/-! ## §3  `M⁽³⁾`'s branch flag

Base II.1.M keeps the whole of `A₀` on both sides, so `M⁽³⁾` is anchored at
`block.1` itself: its branch vertex is the `t₂` endpoint above `A₀`, carrying
`e₁`, `e₂` and the single regrown occurrence. -/

/-- **The branch flag of `M⁽³⁾`.**  `e₁` and `e₂` are retained; `e₃` goes to
the single regrown occurrence above `A₀`. -/
noncomputable def joinedFlag (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) (edge : data.SourceEdge) :
    (joinedCandidate star geometry).datum.SourceEdge :=
  if edge.1.1 = star.edge profile.singleLabel then
    (joinedCandidate star geometry).newSourceEdge block.1
  else (joinedCandidate star geometry).oldSourceEdge edge

theorem joinedFlag_single (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) {edge : data.SourceEdge}
    (hTarget : edge.1.1 = star.edge profile.singleLabel) :
    joinedFlag profile geometry edge =
      (joinedCandidate star geometry).newSourceEdge block.1 := if_pos hTarget

theorem joinedFlag_not_single (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) {edge : data.SourceEdge}
    (hTarget : ¬ edge.1.1 = star.edge profile.singleLabel) :
    joinedFlag profile geometry edge =
      (joinedCandidate star geometry).oldSourceEdge edge := if_neg hTarget

/-- **The flag dictionary at `M⁽³⁾`'s branch vertex.** -/
theorem joined_selectedFlag_star (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    nonDanglingIncident (joinedCandidate star geometry).datum
        ((joinedCandidate star geometry).datum.sourceEndpoint
          (wallSide target wall (sideOf profile.doubleLabel)) block.1) =
      (nonDanglingIncident data (data.sourceEndpoint wall block.1)).image
        (joinedFlag profile geometry) := by
  classical
  have hFirst := joinedFlag_not_single profile geometry (first_target_ne profile)
  have hSecond := joinedFlag_not_single profile geometry (second_target_ne profile)
  have hThird := joinedFlag_single profile geometry profile.third_target
  rw [joined_nonDanglingIncident_double input shape geometry block.1
      (block_rel_self data wall block),
    incoming_star profile]
  simp only [Finset.image_insert, Finset.image_singleton, hFirst, hSecond, hThird]

theorem joined_flag_distinct (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) :
    joinedFlag profile geometry profile.first.1 ≠
        joinedFlag profile geometry profile.second.1 ∧
      joinedFlag profile geometry profile.first.1 ≠
        joinedFlag profile geometry profile.third.1 ∧
      joinedFlag profile geometry profile.second.1 ≠
        joinedFlag profile geometry profile.third.1 := by
  have hFirst := joinedFlag_not_single profile geometry (first_target_ne profile)
  have hSecond := joinedFlag_not_single profile geometry (second_target_ne profile)
  have hThird := joinedFlag_single profile geometry profile.third_target
  refine ⟨?_, ?_, ?_⟩
  · rw [hFirst, hSecond]
    exact fun hEqual ↦ first_ne_second_edge profile
      (ResolutionCut.oldSourceEdge_injective _ hEqual)
  · rw [hFirst, hThird]
    exact oldSourceEdge_ne_newSourceEdge _ _
  · rw [hSecond, hThird]
    exact oldSourceEdge_ne_newSourceEdge _ _

theorem joined_selectedFlag_injOn
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) :
    Set.InjOn (joinedFlag profile geometry)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall block.1)) := by
  classical
  obtain ⟨h12, h13, h23⟩ := joined_flag_distinct profile geometry
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
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hNotBranch : (joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet ≠
      (joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall (sideOf profile.doubleLabel)) block.1) :
    nonDanglingValency (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet) ≤ 2 := by
  rcases Shape.label_cases profile (sideLabel side) with hLabel | hLabel
  · have hSide : side = sideOf profile.doubleLabel := side_eq_sideOf hLabel
    subst hSide
    exact absurd (joined_endpoint_eq geometry (sideOf profile.doubleLabel) hRel).symm
      hNotBranch
  · have hSide : side = sideOf profile.singleLabel := side_eq_sideOf hLabel
    subst hSide
    have := joined_nonDanglingValency_single input shape geometry sheet hRel
    omega

/-- **The flag preserves stable rows.**  `e₁` and `e₂` are retained; `e₃` and
the regrown occurrence are consecutive at the divalent `t₃` endpoint
(`joined_new_stablePath_eq_third`). -/
theorem joined_selectedFlag_row (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall block.1))
    (hFlag : ¬ IsDangling (joinedCandidate star geometry).datum
      (joinedFlag profile geometry edge)) :
    NonDanglingEdge.stablePath (⟨joinedFlag profile geometry edge, hFlag⟩ :
        NonDanglingEdge (joinedCandidate star geometry).datum) =
      (retainedEdge (joinedCandidate star geometry) input.valid.1
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
    exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext (joinedFlag_single profile geometry hTarget)))
      (joined_new_stablePath_eq_third input shape geometry block.1
        (block_rel_self data wall block))
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (joinedFlag_not_single profile geometry hTarget))

/-- **Figure 33's `M⁽³⁾` as the core's `GraphData`.**  `selectedSide` is
`sideOf profile.doubleLabel`: its branch vertex is the `t₂` endpoint above
`A₀`. -/
noncomputable def joinedGraphData (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) : GraphData data wall where
  toSelectedData := joinedSelectedData input shape geometry
  selectedSide := sideOf profile.doubleLabel
  selectedFlag := joinedFlag profile geometry
  selectedFlag_star := joined_selectedFlag_star input shape geometry
  selectedFlag_injOn := joined_selectedFlag_injOn profile geometry
  selected_not_branch := joined_selected_not_branch input shape geometry
  selectedFlag_row := joined_selectedFlag_row input shape geometry

@[simp] theorem joinedGraphData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedGraphData input shape geometry).candidate = joinedCandidate star geometry := rfl

@[simp] theorem joinedGraphData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedGraphData input shape geometry).selected = block.1 := rfl

@[simp] theorem joinedGraphData_selectedSide (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedGraphData input shape geometry).selectedSide = sideOf profile.doubleLabel := rfl

theorem joinedGraphData_stablePathEquiv (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedGraphData input shape geometry).stablePathEquiv =
      joinedStablePathEquiv input shape geometry := rfl

/-! ## §4  The two stable incidence graphs -/

/-- **`M⁽²⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def dividedEquivalence (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    StableGraphIncidence.Equivalence data (DividedData.candidate shape divided).datum :=
  (dividedGraphData input shape divided).equivalence

/-- **Its row map is literally `W2M1kRowDescent`'s bijection**, so every
`W2M1kLimitMatrix` evaluation reads the same rows this dictionary does. -/
theorem dividedEquivalence_rowEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    (dividedEquivalence input shape divided).row =
      dividedStablePathEquiv input shape divided := rfl

@[simp] theorem dividedEquivalence_row (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (path : StablePath data) :
    (dividedEquivalence input shape divided).row path =
      dividedStablePathEquiv input shape divided path := rfl

/-- **`M⁽³⁾`'s stable incidence graph is the incoming one.** -/
noncomputable def joinedEquivalence (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    StableGraphIncidence.Equivalence data (joinedCandidate star geometry).datum :=
  (joinedGraphData input shape geometry).equivalence

theorem joinedEquivalence_rowEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    (joinedEquivalence input shape geometry).row =
      joinedStablePathEquiv input shape geometry := rfl

@[simp] theorem joinedEquivalence_row (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    (joinedEquivalence input shape geometry).row path =
      joinedStablePathEquiv input shape geometry path := rfl

/-- Path ends transport to `M⁽²⁾`. -/
theorem divided_hasPathEnds (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (hEnds : HasPathEnds data) :
    HasPathEnds (DividedData.candidate shape divided).datum :=
  (dividedGraphData input shape divided).hasPathEnds hEnds

/-- Path ends transport to `M⁽³⁾`. -/
theorem joined_hasPathEnds (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (hEnds : HasPathEnds data) :
    HasPathEnds (joinedCandidate star geometry).datum :=
  (joinedGraphData input shape geometry).hasPathEnds hEnds

end DraismaVargas.LocalCases.W2M1kGraphData
