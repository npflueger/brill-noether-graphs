import DraismaVargas.LocalCases.W2M1kStableGraph

/-!
# Figure 33's induced stable-row map

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}` and Figure 33; the
induced-labelling paragraph of the `{w2-r2}` preamble.

The stable lift is the generic one, `LimitChainCore.LiftData.stablePathLift`:
retain any surviving occurrence of an old stable path.  What this module
supplies is the reading of Figure 33's **divalent** members as the core's data,
and nothing else is added: every hypothesis below is already carried by
`W2M1kStableGraph`'s census.

* `dividedWallCandidate` / `joinedWallCandidate` -- `M⁽²⁾` and `M⁽³⁾` are the
  two-star members, so each retains `star.edge 0` at the old endpoint and sends
  `star.edge 1` to the fresh one.  Unlike M-kk, **which** of `t₂`, `t₃` that is
  is not fixed by the bundle (`W2M1kStableGraph` §2), so `retainedTarget` is
  `star.edge 0` and every selected-endpoint field below is discharged by cases
  on `Shape.label_cases profile (sideLabel side)`;
* `dividedBackgroundShape` / `joinedBackgroundShape` -- off `A₀` both members
  install `ResolutionM11.joinedResolutionAt`, which agrees with `star.edge 0`'s
  own star **block by block** because every background wall block has local
  ramification zero (`W2M1kStableGraph.background_blockCount_local`);
* `dividedLiftData` / `joinedLiftData` -- the distinguished incoming source
  vertex is the case's own `w2-r2-nd3` branch vertex, of surviving valency
  three, so no consecutive pair of the incoming stable quotient meets it;
* `dividedSelectedData` / `joinedSelectedData` -- the `A₀` half of
  `W2M1kStableGraph`'s census, read as the core's `SelectedData`, which gives
  surjectivity here and the reverse map, hence injectivity, in
  `W2M1kRowDescent`.

## The anchors are chosen for the downstream modules

`LimitChainCore.GraphData` reads the member's branch vertex above the expanded
endpoint of the bundle's own anchor `selected`, so the anchor is fixed here
rather than re-anchored downstream (M-kk needed `W2MkkGraphData.reanchor`
because `W2MkkStableLift` anchored at `block.1`).  `M⁽³⁾` keeps the whole wall
block at both endpoints, so `block.1` serves; `M⁽²⁾`'s branch vertex is its
`t₃`-side endpoint over `A₀ ∖ {q}`, and `block.1` may *be* `q`, so it is
anchored at `pinSheet profile profile.doubleLabel`, which
`W2M1kStableGraph.divided_pin_ne` separates from `q`.  Both anchors lie in `A₀`
and `LimitChainCore.backgroundColumn` does not see the difference
(`W2M1kLimitMatrix.backgroundColumn_congr`).

## The leaf member `M⁽¹⁾` is **not** a `WallCandidate`

Base I.a's member has target valencies `(1, 3)`: its retained endpoint is a
target leaf and carries **no** wall direction at all
(`W2M1kLeaves.leaf_right`, which is `rfl`).  The core's
`LimitChainCore.WallCandidate` asks for a `retainedTarget` with
`candidate.right retainedTarget = false`, and no such target edge exists, so
`M⁽¹⁾` has no `WallCandidate`, hence no `BackgroundShape`, `LiftData` or
`SelectedData`.  That obstruction is recorded as a theorem below,
`leaf_not_wallCandidate`; the bespoke leaf chain `W2M1kLeafStableLift`,
`W2M1kLeafRowDescent`, `W2M1kLeafLimitMatrix` treats `M⁽¹⁾` instead.

## Member 2 over the branch-swapped datum

Nothing below is transported.  `W2M1kStableGraph`'s docstring records why:
a given datum carries `M⁽¹⁾` or `M⁽²⁾` and never both, so there is no member-2
candidate over the original datum whose data could be pushed forward.  Member 2
of `W2M1kSwapped.SwappedBundle.candidates` is obtained by instantiating the
definitions below at `W2M1kSwapped.swappedData` with a transported
`W2SourceInput`, `SourceProfile`, `Shape` and `DividedData`.
-/

namespace DraismaVargas.LocalCases.W2M1kStableLift

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open LimitChainCore (WallCandidate BackgroundShape LiftData SelectedData pasted wallSide
  sourceEndpoint_eq_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §0  The side dictionary, completed

`W2M1kStableGraph` §2 proves `sideLabel (sideOf label) = label`.  The two
divalent members below need the other composite as well, so that a hypothesis
`sideLabel side = profile.doubleLabel` can be turned into a substitution for
`side`. -/

@[simp] theorem sideOf_sideLabel (side : Bool) : sideOf (sideLabel side) = side := by
  cases side <;> rfl

/-- Which side of the new edge a wall direction is sent to, read off the label
that side carries. -/
theorem side_eq_sideOf {side : Bool} {label : Fin 2} (hLabel : sideLabel side = label) :
    side = sideOf label := by
  rw [← hLabel, sideOf_sideLabel]

/-! ## §1  What the two divalent members share

Both `M⁽²⁾` and `M⁽³⁾` carry the two-star's own side assignment, so both retain
`star.edge 0` at the old endpoint and nothing else. -/

/-- A member carrying the two-star's side assignment retains `star.edge 0` and
no other wall direction. -/
theorem unique_zero_of_right (candidate : BalancedGlobal.Candidate target degree data wall)
    (hRight : ∀ edge : target.edges, candidate.right edge = star.right edge)
    (edge : target.edges) (hMem : edge ∈ GluingDatum.incidentEdges wall)
    (hFalse : candidate.right edge = false) : edge = star.edge 0 := by
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hMem⟩
  have hEdge : edge = star.edge label := (congrArg Subtype.val hLabel).symm
  have hCases : label = 0 ∨ label = 1 := by omega
  rcases hCases with rfl | rfl
  · exact hEdge
  · rw [hEdge, hRight, star.right_edge_one] at hFalse
    exact Bool.noConfusion hFalse

/-- **The background block identity both divalent members share.**  Off `A₀`
the direction `star.edge 0` induces exactly one class, so a member retaining
the whole wall block there retains that direction's own star. -/
theorem wall_block_eq_zero_block (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (data.vertexPartition wall).block sheet =
      (data.edgePartition (star.edge 0)).block sheet :=
  (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data 0) sheet
    (background_blockCount_local input profile 0 sheet hSheet)).symm

/-- **The distinguished incoming source vertex is not divalent**, read at any
sheet of `A₀`: it is the case's own `w2-r2-nd3` branch vertex, whose surviving
valency the profile records as three. -/
theorem selected_valency_ne_two (profile : W2R2SourceProfile.SourceProfile data star block)
    {anchor : Fin degree} (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    nonDanglingValency data (data.sourceEndpoint wall anchor) ≠ 2 := by
  have hValency : nonDanglingValency data (data.sourceEndpoint wall block.1) = 3 :=
    profile.valency
  rw [← sourceEndpoint_eq_of_rel data wall hAnchor]
  omega

/-- A sheet of `A₀` distinct from both of the profile's named sheets is
distinct from both pinned sheets. -/
theorem ne_pinSheet_of_ne (profile : W2R2SourceProfile.SourceProfile data star block)
    {sheet : Fin degree} (label : Fin 2)
    (hDouble : sheet ≠ pinSheet profile profile.doubleLabel)
    (hSingle : sheet ≠ pinSheet profile profile.singleLabel) :
    sheet ≠ pinSheet profile label := by
  rcases pinSheet_cases profile label with hEq | hEq <;> rw [hEq]
  · exact hDouble
  · exact hSingle

/-! ## §2  The divided member `M⁽²⁾` -/

/-- `M⁽²⁾` retains `star.edge 0` and nothing else at the old endpoint. -/
noncomputable def dividedWallCandidate (shape : Shape profile) (divided : DividedData profile) :
    WallCandidate data wall where
  candidate := DividedData.candidate shape divided
  retainedTarget := star.edge 0
  target_mem := star.edge_mem_incidentEdges 0
  left := (divided_right shape divided _).trans star.right_edge_zero
  unique := fun edge hMem hFalse ↦
    unique_zero_of_right (DividedData.candidate shape divided)
      (divided_right shape divided) edge hMem hFalse

/-! ### The divided member's pasted blocks off `A₀` -/

theorem divided_pasted_left_block (shape : Shape profile) (divided : DividedData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted (DividedData.candidate shape divided)).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, divided_background_resolution shape divided _
    (background_repr profile sheet hSheet)]
  rfl

theorem divided_pasted_right_block (shape : Shape profile) (divided : DividedData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted (DividedData.candidate shape divided)).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, divided_background_resolution shape divided _
    (background_repr profile sheet hSheet)]
  rfl

theorem divided_pasted_newEdge_block (shape : Shape profile) (divided : DividedData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (pasted (DividedData.candidate shape divided)).newEdge.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (DividedData.candidate shape divided).resolution
    (DividedData.candidate shape divided).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, divided_background_resolution shape divided _
    (background_repr profile sheet hSheet)]
  rfl

/-- A sheet outside `A₀` is outside the anchor's class, for the divided
member's anchor `pinSheet profile profile.doubleLabel`. -/
theorem divided_background (profile : W2R2SourceProfile.SourceProfile data star block)
    {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel (pinSheet profile profile.doubleLabel) sheet) :
    ¬ (data.vertexPartition wall).Rel block.1 sheet :=
  fun hRel ↦ hSheet ((pinSheet_rel profile.doubleLabel).symm.trans hRel)

/-- Off `A₀` `M⁽²⁾` installs `star.edge 0`'s own star, block by block: the
joined background retains the whole wall block, and that direction induces
exactly one class there. -/
noncomputable def dividedBackgroundShape (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) : BackgroundShape data wall where
  toWallCandidate := dividedWallCandidate shape divided
  selected := pinSheet profile profile.doubleLabel
  left_block := fun {_} hSheet ↦
    (divided_pasted_left_block shape divided (divided_background profile hSheet)).trans
      (wall_block_eq_zero_block input profile (divided_background profile hSheet))
  right_block := fun {_} hSheet ↦
    divided_pasted_right_block shape divided (divided_background profile hSheet)
  newEdge_block := fun {_} hSheet ↦
    (divided_pasted_newEdge_block shape divided (divided_background profile hSheet)).trans
      (wall_block_eq_zero_block input profile (divided_background profile hSheet))
  genus_eq := divided_sourceGenus shape divided

/-- `A₀` has surviving valency three, so retention respects the incoming stable
quotient. -/
noncomputable def dividedLiftData (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) : LiftData data wall where
  toBackgroundShape := dividedBackgroundShape input shape divided
  valid := input.valid
  selected_valency_ne_two := selected_valency_ne_two profile (pinSheet_rel profile.doubleLabel)

/-! ### The `A₀` census of `M⁽²⁾`, in the core's shape -/

/-- The old occurrence a selected regrown occurrence of `M⁽²⁾` represents:
`e₁` through its own sheet, `e₂` everywhere else.  Over `e₄`'s sheet the value
is irrelevant -- that regrown occurrence is pruned
(`W2M1kStableGraph.divided_new_deleted_dangling`) -- but it must still name an
incoming survivor, so `e₂` serves. -/
noncomputable def dividedRep (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree) : data.SourceEdge :=
  if sheet = pinSheet profile profile.doubleLabel then profile.first.1 else profile.second.1

@[simp] theorem dividedRep_pin (profile : W2R2SourceProfile.SourceProfile data star block) :
    dividedRep profile (pinSheet profile profile.doubleLabel) = profile.first.1 :=
  if_pos rfl

theorem dividedRep_of_ne (profile : W2R2SourceProfile.SourceProfile data star block)
    {sheet : Fin degree} (hNe : sheet ≠ pinSheet profile profile.doubleLabel) :
    dividedRep profile sheet = profile.second.1 :=
  if_neg hNe

theorem dividedRep_survives (profile : W2R2SourceProfile.SourceProfile data star block)
    (sheet : Fin degree) : ¬ IsDangling data (dividedRep profile sheet) := by
  unfold dividedRep
  split_ifs
  · exact profile.first_survives
  · exact profile.second_survives

/-- Selected sheets carrying one regrown occurrence of `M⁽²⁾` carry one
representative: `e₁`'s sheet is a singleton block of the member's new edge. -/
theorem dividedRep_congr (shape : Shape profile) (divided : DividedData profile)
    (first second : Fin degree)
    (hEqual : (DividedData.candidate shape divided).newSourceEdge first =
      (DividedData.candidate shape divided).newSourceEdge second) :
    dividedRep profile first = dividedRep profile second := by
  unfold dividedRep
  by_cases hFirst : first = pinSheet profile profile.doubleLabel
  · by_cases hSecond : second = pinSheet profile profile.doubleLabel
    · rw [if_pos hFirst, if_pos hSecond]
    · refine absurd ?_ (divided_newSourceEdge_pin_ne shape divided profile.doubleLabel
        second hSecond)
      rw [← hFirst]
      exact hEqual
  · by_cases hSecond : second = pinSheet profile profile.doubleLabel
    · refine absurd ?_ (divided_newSourceEdge_pin_ne shape divided profile.doubleLabel
        first hFirst)
      rw [← hSecond]
      exact hEqual.symm
    · rw [if_neg hFirst, if_neg hSecond]

/-- **Every surviving regrown occurrence of `M⁽²⁾` above `A₀` lies in the row of
its representative.**  Over `e₄`'s sheet there is nothing to say: that
occurrence is pruned. -/
theorem divided_selected_new_stablePath (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hSurvives : ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge sheet))
    (hRep : ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).oldSourceEdge (dividedRep profile sheet))) :
    NonDanglingEdge.stablePath
        (⟨(DividedData.candidate shape divided).newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge (DividedData.candidate shape divided).datum) =
      NonDanglingEdge.stablePath
        (⟨(DividedData.candidate shape divided).oldSourceEdge (dividedRep profile sheet),
          hRep⟩ : NonDanglingEdge (DividedData.candidate shape divided).datum) := by
  by_cases hDouble : sheet = pinSheet profile profile.doubleLabel
  · subst hDouble
    refine (divided_new_unit_stablePath_eq input shape divided).trans ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg (DividedData.candidate shape divided).oldSourceEdge
        (dividedRep_pin profile).symm))
  · by_cases hSingle : sheet = pinSheet profile profile.singleLabel
    · subst hSingle
      exact absurd (divided_new_deleted_dangling input shape divided) hSurvives
    · have hEqual : (DividedData.candidate shape divided).newSourceEdge sheet =
          (DividedData.candidate shape divided).newSourceEdge divided.third :=
        divided_newSourceEdge_eq_third shape divided sheet hRel
          (ne_pinSheet_of_ne profile 0 hDouble hSingle)
          (ne_pinSheet_of_ne profile 1 hDouble hSingle)
      refine Eq.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext hEqual : (⟨_, hSurvives⟩ :
          NonDanglingEdge (DividedData.candidate shape divided).datum) =
            ⟨_, divided_new_third_survives input shape divided⟩)) ?_
      refine (divided_new_third_stablePath_eq input shape divided).trans ?_
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (congrArg (DividedData.candidate shape divided).oldSourceEdge
          (dividedRep_of_ne profile hDouble).symm))

/-- **The surviving pair at a divalent selected endpoint of `M⁽²⁾`**, on either
side of the new edge.  On the side carrying `t₂` both selected endpoints are
divalent, and the pair is `e₁` with the regrown singleton over `e₁`'s sheet or
`e₂` with the residual regrown occurrence; on the side carrying `t₃` no
selected endpoint is divalent at all, its surviving valencies being `0` over
`e₄`'s sheet and `3` everywhere else. -/
theorem divided_selected_pair (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (side : Bool) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hValency : nonDanglingValency (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).datum.sourceEndpoint
        (wallSide target wall side) sheet) = 2) :
    ∃ other : Fin degree, (data.vertexPartition wall).Rel (pinSheet profile 0) other ∧
      nonDanglingIncident (DividedData.candidate shape divided).datum
          ((DividedData.candidate shape divided).datum.sourceEndpoint
            (wallSide target wall side) sheet) =
        {(DividedData.candidate shape divided).newSourceEdge other,
          (DividedData.candidate shape divided).oldSourceEdge (dividedRep profile other)} := by
  rcases Shape.label_cases profile (sideLabel side) with hLabel | hLabel
  · have hSide : side = sideOf profile.doubleLabel := side_eq_sideOf hLabel
    subst hSide
    by_cases hPin : sheet = pinSheet profile profile.doubleLabel
    · subst hPin
      refine ⟨pinSheet profile profile.doubleLabel,
        pin_rel_pin profile 0 profile.doubleLabel, ?_⟩
      rw [divided_nonDanglingIncident_unit input shape divided, dividedRep_pin]
      exact Finset.pair_comm _ _
    · refine ⟨divided.third, divided.rel_third, ?_⟩
      rw [divided_nonDanglingIncident_pair input shape divided sheet hRel hPin,
        dividedRep_of_ne profile (divided_third_ne_pin divided profile.doubleLabel)]
      exact Finset.pair_comm _ _
  · exfalso
    have hSide : side = sideOf profile.singleLabel := side_eq_sideOf hLabel
    subst hSide
    by_cases hPin : sheet = pinSheet profile profile.singleLabel
    · subst hPin
      rw [divided_nonDanglingValency_deleted input shape divided] at hValency
      omega
    · rw [divided_nonDanglingValency_branch input shape divided sheet hRel hPin] at hValency
      omega

/-- The `A₀` half of `W2M1kStableGraph`'s divided census, read as the core's
selected data, anchored at `e₁`'s sheet. -/
noncomputable def dividedSelectedData (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) : SelectedData data wall where
  toLiftData := dividedLiftData input shape divided
  selectedRep := dividedRep profile
  selectedRep_survives := fun sheet _ ↦ dividedRep_survives profile sheet
  selectedRep_congr := fun first second _ _ hEqual ↦
    dividedRep_congr shape divided first second hEqual
  selected_new_stablePath := fun sheet hRel hSurvives hRep ↦
    divided_selected_new_stablePath input shape divided sheet
      ((pin_rel_pin profile 0 profile.doubleLabel).trans hRel) hSurvives hRep
  selected_left_pair := by
    intro sheet hRel hValency
    obtain ⟨other, hOther, hStar⟩ := divided_selected_pair input shape divided false sheet
      ((pin_rel_pin profile 0 profile.doubleLabel).trans hRel) hValency
    exact ⟨other, (pin_rel_pin profile profile.doubleLabel 0).trans hOther, hStar⟩
  selected_right_pair := by
    intro sheet hRel hValency
    obtain ⟨other, hOther, hStar⟩ := divided_selected_pair input shape divided true sheet
      ((pin_rel_pin profile 0 profile.doubleLabel).trans hRel) hValency
    exact ⟨other, (pin_rel_pin profile profile.doubleLabel 0).trans hOther, hStar⟩

@[simp] theorem dividedSelectedData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedSelectedData input shape divided).candidate = DividedData.candidate shape divided :=
  rfl

@[simp] theorem dividedSelectedData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedSelectedData input shape divided).selected =
      pinSheet profile profile.doubleLabel := rfl

@[simp] theorem dividedSelectedData_selectedRep (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (sheet : Fin degree) :
    (dividedSelectedData input shape divided).selectedRep sheet = dividedRep profile sheet := rfl

@[simp] theorem dividedSelectedData_retainedTarget (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    (dividedSelectedData input shape divided).retainedTarget = star.edge 0 := rfl

/-! ## §3  The joined member `M⁽³⁾` -/

/-- `M⁽³⁾` retains `star.edge 0` and nothing else at the old endpoint. -/
noncomputable def joinedWallCandidate (star : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) : WallCandidate data wall where
  candidate := joinedCandidate star geometry
  retainedTarget := star.edge 0
  target_mem := star.edge_mem_incidentEdges 0
  left := (joined_right geometry _).trans star.right_edge_zero
  unique := fun edge hMem hFalse ↦
    unique_zero_of_right (joinedCandidate star geometry) (joined_right geometry) edge hMem hFalse

/-- Off `A₀` `M⁽³⁾` installs `star.edge 0`'s own star, block by block.  It keeps
the whole wall block everywhere, so the three identities are the one background
count. -/
noncomputable def joinedBackgroundShape (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) : BackgroundShape data wall where
  toWallCandidate := joinedWallCandidate star geometry
  selected := block.1
  left_block := fun {sheet} hSheet ↦
    (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pastedSide geometry false)).trans (wall_block_eq_zero_block input profile hSheet)
  right_block := fun {sheet} _ ↦
    congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pastedSide geometry true)
  newEdge_block := fun {sheet} hSheet ↦
    (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pasted_newEdge geometry)).trans (wall_block_eq_zero_block input profile hSheet)
  genus_eq := joined_sourceGenus geometry

noncomputable def joinedLiftData (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) : LiftData data wall where
  toBackgroundShape := joinedBackgroundShape input profile geometry
  valid := input.valid
  selected_valency_ne_two := selected_valency_ne_two profile rfl

/-- **The surviving pair at a divalent selected endpoint of `M⁽³⁾`**: the
retained `e₃` and the one regrown occurrence.  On the side carrying `t₂` the
selected endpoint is the member's branch vertex and is never divalent. -/
theorem joined_selected_pair (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (side : Bool) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet)
    (hValency : nonDanglingValency (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).datum.sourceEndpoint
        (wallSide target wall side) sheet) = 2) :
    ∃ other : Fin degree, (data.vertexPartition wall).Rel block.1 other ∧
      nonDanglingIncident (joinedCandidate star geometry).datum
          ((joinedCandidate star geometry).datum.sourceEndpoint
            (wallSide target wall side) sheet) =
        {(joinedCandidate star geometry).newSourceEdge other,
          (joinedCandidate star geometry).oldSourceEdge profile.third.1} := by
  rcases Shape.label_cases profile (sideLabel side) with hLabel | hLabel
  · exfalso
    have hSide : side = sideOf profile.doubleLabel := side_eq_sideOf hLabel
    subst hSide
    rw [joined_nonDanglingValency_double input shape geometry sheet hSheet] at hValency
    omega
  · have hSide : side = sideOf profile.singleLabel := side_eq_sideOf hLabel
    subst hSide
    refine ⟨sheet, hSheet, ?_⟩
    rw [joined_nonDanglingIncident_single input shape geometry sheet hSheet]
    exact Finset.pair_comm _ _

/-- The `A₀` half of `W2M1kStableGraph`'s joined census, read as the core's
selected data.  Every selected sheet's regrown occurrence represents `e₃`. -/
noncomputable def joinedSelectedData (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) : SelectedData data wall where
  toLiftData := joinedLiftData input profile geometry
  selectedRep := fun _ ↦ profile.third.1
  selectedRep_survives := fun _ _ ↦ profile.third_survives
  selectedRep_congr := fun _ _ _ _ _ ↦ rfl
  selected_new_stablePath := fun sheet hRel _ _ ↦
    joined_new_stablePath_eq_third input shape geometry sheet hRel
  selected_left_pair := fun sheet hRel hValency ↦
    joined_selected_pair input shape geometry false sheet hRel hValency
  selected_right_pair := fun sheet hRel hValency ↦
    joined_selected_pair input shape geometry true sheet hRel hValency

@[simp] theorem joinedSelectedData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedSelectedData input shape geometry).candidate = joinedCandidate star geometry := rfl

@[simp] theorem joinedSelectedData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedSelectedData input shape geometry).selected = block.1 := rfl

@[simp] theorem joinedSelectedData_selectedRep (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree) :
    (joinedSelectedData input shape geometry).selectedRep sheet = profile.third.1 := rfl

@[simp] theorem joinedSelectedData_retainedTarget (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    (joinedSelectedData input shape geometry).retainedTarget = star.edge 0 := rfl

/-! ## §4  The stable lifts -/

/-- **Figure 33's induced stable-row map for `M⁽²⁾`**, evaluated by retaining
any actual surviving occurrence of the old row. -/
noncomputable def dividedStablePathLift (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    StablePath data → StablePath (DividedData.candidate shape divided).datum :=
  (dividedLiftData input shape divided).stablePathLift

@[simp] theorem dividedStablePathLift_mk (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (edge : NonDanglingEdge data) :
    dividedStablePathLift input shape divided edge.stablePath =
      (retainedEdge (DividedData.candidate shape divided) input.valid.1 edge).stablePath := rfl

/-- Retaining a different occurrence of one old stable row gives the same row
upstairs. -/
theorem divided_stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (DividedData.candidate shape divided) input.valid.1 first).stablePath =
      (retainedEdge (DividedData.candidate shape divided) input.valid.1 second).stablePath :=
  (dividedLiftData input shape divided).retained_stablePath_eq_of_consecutive first second
    hConsecutive

/-- No stable row of `M⁽²⁾` lies entirely in the new fibre. -/
theorem divided_exists_retained_row (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile)
    (edge : NonDanglingEdge (DividedData.candidate shape divided).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (DividedData.candidate shape divided) input.valid.1 old).stablePath =
        edge.stablePath :=
  (dividedSelectedData input shape divided).exists_retained_row edge

theorem divided_stablePathLift_surjective (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    Function.Surjective (dividedStablePathLift input shape divided) :=
  (dividedSelectedData input shape divided).stablePathLift_surjective

/-- **Figure 33's induced stable-row map for `M⁽³⁾`.** -/
noncomputable def joinedStablePathLift (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) :
    StablePath data → StablePath (joinedCandidate star geometry).datum :=
  (joinedLiftData input profile geometry).stablePathLift

@[simp] theorem joinedStablePathLift_mk (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) (edge : NonDanglingEdge data) :
    joinedStablePathLift input profile geometry edge.stablePath =
      (retainedEdge (joinedCandidate star geometry) input.valid.1 edge).stablePath := rfl

theorem joined_stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (joinedCandidate star geometry) input.valid.1 first).stablePath =
      (retainedEdge (joinedCandidate star geometry) input.valid.1 second).stablePath :=
  (joinedLiftData input profile geometry).retained_stablePath_eq_of_consecutive first second
    hConsecutive

theorem joined_exists_retained_row (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (edge : NonDanglingEdge (joinedCandidate star geometry).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (joinedCandidate star geometry) input.valid.1 old).stablePath =
        edge.stablePath :=
  (joinedSelectedData input shape geometry).exists_retained_row edge

theorem joined_stablePathLift_surjective (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    Function.Surjective (joinedStablePathLift input profile geometry) :=
  (joinedSelectedData input shape geometry).stablePathLift_surjective

/-! ## §5  The leaf member `M⁽¹⁾` has no `WallCandidate`

Base I.a's member sends **both** wall directions to the fresh endpoint
(`W2M1kLeaves.leaf_right`), so its retained endpoint is the target leaf of
`leaf_target_valencies` and carries no wall direction.  The core's
`LimitChainCore.WallCandidate` names the one wall direction a member retains
*at the retained endpoint*, so there is nothing to name: the field `left` is
unsatisfiable, and with it every structure extending `WallCandidate`. -/

/-- **The leaf member defeats `LimitChainCore.WallCandidate`.**  Not at the
background block identities and not at any census field: at `left`, the very
first field, because `M⁽¹⁾` retains no wall direction at all. -/
theorem leaf_not_wallCandidate (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (candidate : WallCandidate data wall)
    (hCandidate : candidate.candidate = LeafPair.candidate input shape pair) : False := by
  have hLeft : (LeafPair.candidate input shape pair).right candidate.retainedTarget = false := by
    rw [← hCandidate]
    exact candidate.left
  rw [leaf_right input shape pair candidate.retainedTarget] at hLeft
  exact Bool.noConfusion hLeft

/-- The same statement without a bundled `WallCandidate`: no target edge is
retained at `M⁽¹⁾`'s old endpoint. -/
theorem leaf_no_retained_direction (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : target.edges) :
    (LeafPair.candidate input shape pair).right edge ≠ false := by
  rw [leaf_right input shape pair edge]
  exact Bool.noConfusion

end DraismaVargas.LocalCases.W2M1kStableLift
