module

public import DraismaVargas.LocalCases.W2MkkStableGraph

@[expose] public section

/-!
# Figure 34's induced stable-row map

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-kk} (abbreviated M-kk),
Figure 34; the induced-labelling paragraph at the start of Case {w2-r2}.

The stable lift is the generic one, `LimitChainCore.LiftData.stablePathLift`:
retain any surviving occurrence of an old stable path.  What this module
supplies is the reading of Figure 34's three members as the core's data, and
nothing else is added: every hypothesis below is already carried by
`W2MkkStableGraph`'s census.

* `detachWallCandidate` / `joinedWallCandidate` — every member retains `t₂`
  (`profile.doubleLabel`) at the old endpoint and sends `t₃` to the fresh one;
* `detachBackgroundShape` / `joinedBackgroundShape` — off `A₀` both members
  install `ResolutionM11.joinedResolutionAt`, which agrees with `t₂`'s own star
  **block by block** because every background wall block has local ramification
  zero (`W2MkkStableGraph.background_blockCount_local`).  This is the reason the
  core records three block identities rather than `resolution_eq`: M-kk is an
  M11-family member and its background local resolution is *not* `t₂`'s fine
  star as a `LocalResolution`;
* `detachLiftData` / `joinedLiftData` — `A₀` has surviving valency three, so no
  consecutive pair of the incoming stable quotient meets it;
* `detachSelectedData` / `joinedSelectedData` — the `A₀` half of
  `W2MkkStableGraph`'s census, read as the core's `SelectedData`, which gives
  surjectivity here and the reverse map, hence injectivity, in
  `W2MkkRowDescent`.

## The one new census lemma

The core's `LiftData` asks that the incoming distinguished source vertex is not
divalent.  For M-kk that is `selected_valency_ne_two` below, and it is **not**
the M11 route (`M11JoinedStableLift.background_of_wall_valency_two`, which case
P uses): the M-kk branch vertex is the incoming `w2-r2-nd3` vertex itself, whose
surviving valency the profile records as three.  So the lemma is one line off
`W2R2SourceProfile.SourceProfile.valency` and needs no block-cardinality
hypothesis at all.

## The two detaching members

Member 1 and member 2 of Figure 34 are the *same* uniform object here,
`DetachData.candidate`: which of `M⁽¹⁾`, `M⁽²⁾` a datum carries is decided by
the datum, through `W2MkkSourceCandidates.pinSheet_mem`.  Nothing below is
transported across the branch swap; member 2 is obtained by instantiating these
same definitions at the branch-swapped datum, exactly as `W2MkkStableGraph`'s
docstring records.

## What the `t₃` endpoint over `{x}` does to the core's fields

`SelectedData.selected_right_pair` is **vacuous** for a detaching member: above
`A₀` its `t₃` endpoints have surviving valency three (over `A₀ ∖ {x}`) or zero
(over `{x}`, where the new occurrence dies with `e₄` —
`W2MkkStableGraph.detach_new_pin_dangling`), never two.  Symmetrically
`selected_left_pair` is vacuous for `M⁽³⁾`, whose `t₂` endpoint is the branch
vertex.  Both are recorded as the explicit `≠ 2` lemmas
`detach_fresh_valency_ne_two` and `joined_old_valency_ne_two`.
-/

namespace DraismaVargas.LocalCases.W2MkkStableLift

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2MkkSourceCandidates
open W2MkkStableGraph
open LimitChainCore (WallCandidate BackgroundShape LiftData SelectedData)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The new census lemma at the M-kk branch vertex

The core's `LiftData` needs the incoming distinguished source vertex to be
non-divalent.  For `{w2-r2-nd3}` that vertex *is* the case's own branch vertex
and the profile records its surviving valency as three. -/

/-- The distinguished incoming source vertex has surviving valency three. -/
theorem selected_valency_eq_three
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    nonDanglingValency data (data.sourceEndpoint wall block.1) = 3 :=
  profile.valency

/-- **Hence no consecutive pair of the incoming stable quotient meets it.** -/
theorem selected_valency_ne_two
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    nonDanglingValency data (data.sourceEndpoint wall block.1) ≠ 2 := by
  rw [selected_valency_eq_three profile]
  omega

/-! ## The background block identity both members share

Off `A₀` the `t₂` direction induces exactly one class, so a member retaining the
whole wall block there retains `t₂`'s own star block by block. -/

theorem wall_block_eq_double_block (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (data.vertexPartition wall).block sheet =
      (data.edgePartition (star.edge profile.doubleLabel)).block sheet :=
  (SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data _) sheet
    (background_blockCount_local input profile profile.doubleLabel sheet hSheet)).symm

/-! ## The detaching members `M⁽¹⁾`, `M⁽²⁾` -/

/-- A detaching member retains `t₂` and nothing else at the retained
endpoint. -/
noncomputable def detachWallCandidate (shape : Shape profile) (detach : DetachData profile) :
    WallCandidate data wall where
  candidate := detach.candidate shape
  retainedTarget := star.edge profile.doubleLabel
  target_mem := star.edge_mem_incidentEdges _
  left := detach_right_double shape detach
  unique := by
    intro edge hMem hFalse
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hMem⟩
    have hEdge : edge = star.edge label := (congrArg Subtype.val hLabel).symm
    rcases Shape.label_cases profile label with rfl | rfl
    · exact hEdge
    · rw [hEdge, detach_right_single shape detach] at hFalse
      exact Bool.noConfusion hFalse

/-! ### The detaching member's pasted blocks off `A₀` -/

theorem detach_pasted_left_block (shape : Shape profile) (detach : DetachData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (LimitChainCore.pasted (detach.candidate shape)).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteLeft (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_block, detach_background_resolution shape detach _
    (detach_background_repr profile sheet hSheet)]
  rfl

theorem detach_pasted_right_block (shape : Shape profile) (detach : DetachData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (LimitChainCore.pasted (detach.candidate shape)).right.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_block, detach_background_resolution shape detach _
    (detach_background_repr profile sheet hSheet)]
  rfl

theorem detach_pasted_newEdge_block (shape : Shape profile) (detach : DetachData profile)
    {sheet : Fin degree} (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    (LimitChainCore.pasted (detach.candidate shape)).newEdge.block sheet =
      (data.vertexPartition wall).block sheet := by
  show (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (detach.candidate shape).resolution (detach.candidate shape).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_block, detach_background_resolution shape detach _
    (detach_background_repr profile sheet hSheet)]
  rfl

/-- Off `A₀` a detaching member installs `t₂`'s own star, block by block: the
joined background retains the whole wall block and `t₂` induces exactly one
class there. -/
noncomputable def detachBackgroundShape (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) : BackgroundShape data wall where
  toWallCandidate := detachWallCandidate shape detach
  selected := block.1
  left_block := fun {_} hSheet ↦
    (detach_pasted_left_block shape detach hSheet).trans
      (wall_block_eq_double_block input profile hSheet)
  right_block := fun {_} hSheet ↦ detach_pasted_right_block shape detach hSheet
  newEdge_block := fun {_} hSheet ↦
    (detach_pasted_newEdge_block shape detach hSheet).trans
      (wall_block_eq_double_block input profile hSheet)
  genus_eq := detach_sourceGenus shape detach

/-- `A₀` has surviving valency three, so retention respects the incoming stable
quotient. -/
noncomputable def detachLiftData (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) : LiftData data wall where
  toBackgroundShape := detachBackgroundShape input shape detach
  valid := input.valid
  selected_valency_ne_two := selected_valency_ne_two profile

/-! ### The `A₀` census of a detaching member, in the core's shape -/

/-- Selected sheets carrying one regrown occurrence carry one retained `t₂`
representative: the detached new edge refines `t₂`'s occurrence partition. -/
theorem detach_selectedRep_congr (shape : Shape profile) (detach : DetachData profile)
    (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel block.1 first)
    (hEqual : (detach.candidate shape).newSourceEdge first =
      (detach.candidate shape).newSourceEdge second) :
    data.sourceEdge (star.edge profile.doubleLabel) first =
      data.sourceEdge (star.edge profile.doubleLabel) second := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) first :=
    (pinSheet_rel profile).symm.trans hFirst
  have hRel := (detach_pasted_newEdge_rel_iff shape detach first second hWall).mp
    ((LimitChainCore.newSourceEdge_eq_iff_rel first second).mp hEqual)
  exact (LimitChainCore.sourceEdge_eq_iff_rel data _ first second).mpr
    (((endpointPartition profile).detachSheet_refines (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together).rel hRel)

/-- **Every surviving regrown occurrence above `A₀` lies in the row of the
retained `t₂` occurrence through its own sheet.**  Over the pinned sheet there
is nothing to say: that occurrence is pruned. -/
theorem detach_selected_new_stablePath (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet))
    (hRep : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).oldSourceEdge
        (data.sourceEdge (star.edge profile.doubleLabel) sheet))) :
    NonDanglingEdge.stablePath
        (⟨(detach.candidate shape).newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge (detach.candidate shape).datum) =
      NonDanglingEdge.stablePath
        (⟨(detach.candidate shape).oldSourceEdge
            (data.sourceEdge (star.edge profile.doubleLabel) sheet), hRep⟩ :
          NonDanglingEdge (detach.candidate shape).datum) := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hRel
  by_cases hNe : sheet = pinSheet profile
  · subst hNe
    exact absurd (detach_new_pin_dangling input shape detach) hSurvives
  · exact detach_new_stablePath_eq input shape detach sheet hWall hNe

/-- **The surviving pair at a selected `t₂` endpoint of a detaching member.**
Over the pinned sheet the endpoint is the one the partner sheet names. -/
theorem detach_selected_left_pair (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ∃ other : Fin degree, (data.vertexPartition wall).Rel block.1 other ∧
      nonDanglingIncident (detach.candidate shape).datum
          ((detach.candidate shape).datum.sourceEndpoint (oldVertex target wall) sheet) =
        {(detach.candidate shape).newSourceEdge other,
          (detach.candidate shape).oldSourceEdge
            (data.sourceEdge (star.edge profile.doubleLabel) other)} := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hRel
  by_cases hNe : sheet = pinSheet profile
  · subst hNe
    refine ⟨detach.remainder, (pinSheet_rel profile).trans detach.wallTogether, ?_⟩
    rw [LimitChainCore.sourceEndpoint_old_eq_of_rel (pinSheet profile) detach.remainder
        (detach_pasted_left_rel shape detach _ _ rfl detach.together),
      detach_nonDanglingIncident_old input shape detach detach.remainder
        detach.wallTogether (Ne.symm detach.ne_remainder)]
    exact Finset.pair_comm _ _
  · refine ⟨sheet, hRel, ?_⟩
    rw [detach_nonDanglingIncident_old input shape detach sheet hWall hNe]
    exact Finset.pair_comm _ _

/-- **No selected `t₃` endpoint of a detaching member is divalent.**  Over
`A₀ ∖ {x}` it is the member's branch vertex, of surviving valency three; over
`{x}` both incidences are pruned. -/
theorem detach_fresh_valency_ne_two (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (detach.candidate shape).datum
      ((detach.candidate shape).datum.sourceEndpoint (freshVertex target) sheet) ≠ 2 := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile) sheet :=
    (pinSheet_rel profile).symm.trans hRel
  by_cases hNe : sheet = pinSheet profile
  · subst hNe
    rw [detach_nonDanglingValency_fresh_pin input shape detach]
    omega
  · rw [detach_nonDanglingValency_fresh input shape detach sheet hWall hNe]
    omega

/-- The `A₀` half of `W2MkkStableGraph`'s detaching census, read as the core's
selected data. -/
noncomputable def detachSelectedData (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) : SelectedData data wall where
  toLiftData := detachLiftData input shape detach
  selectedRep := fun sheet ↦ data.sourceEdge (star.edge profile.doubleLabel) sheet
  selectedRep_survives := fun sheet hRel ↦ double_sourceEdge_survives_shape shape sheet hRel
  selectedRep_congr := fun first second hFirst _ hEqual ↦
    detach_selectedRep_congr shape detach first second hFirst hEqual
  selected_new_stablePath := fun sheet hRel hSurvives hRep ↦
    detach_selected_new_stablePath input shape detach sheet hRel hSurvives hRep
  selected_left_pair := fun sheet hRel _ ↦
    detach_selected_left_pair input shape detach sheet hRel
  selected_right_pair := fun sheet hRel hValency ↦
    absurd hValency (detach_fresh_valency_ne_two input shape detach sheet hRel)

@[simp] theorem detachSelectedData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachSelectedData input shape detach).candidate = detach.candidate shape := rfl

@[simp] theorem detachSelectedData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachSelectedData input shape detach).selected = block.1 := rfl

@[simp] theorem detachSelectedData_selectedRep (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) (sheet : Fin degree) :
    (detachSelectedData input shape detach).selectedRep sheet =
      data.sourceEdge (star.edge profile.doubleLabel) sheet := rfl

@[simp] theorem detachSelectedData_retainedTarget (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    (detachSelectedData input shape detach).retainedTarget =
      star.edge profile.doubleLabel := rfl

/-! ## The joined member `M⁽³⁾` -/

/-- `M⁽³⁾` retains `t₂` and nothing else at the retained endpoint. -/
noncomputable def joinedWallCandidate
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    WallCandidate data wall where
  candidate := joinedCandidate profile distinguished
  retainedTarget := star.edge profile.doubleLabel
  target_mem := star.edge_mem_incidentEdges _
  left := joined_right_double profile distinguished
  unique := by
    intro edge hMem hFalse
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hMem⟩
    have hEdge : edge = star.edge label := (congrArg Subtype.val hLabel).symm
    rcases Shape.label_cases profile label with rfl | rfl
    · exact hEdge
    · rw [hEdge, joined_right_single profile distinguished] at hFalse
      exact Bool.noConfusion hFalse

/-- Off `A₀` `M⁽³⁾` installs `t₂`'s own star, block by block.  It keeps the whole
wall block everywhere, so the three identities are the one background count. -/
noncomputable def joinedBackgroundShape (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    BackgroundShape data wall where
  toWallCandidate := joinedWallCandidate profile distinguished
  selected := block.1
  left_block := fun {sheet} hSheet ↦
    (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pasted_left profile distinguished)).trans
      (wall_block_eq_double_block input profile hSheet)
  right_block := fun {sheet} _ ↦
    congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pasted_right profile distinguished)
  newEdge_block := fun {sheet} hSheet ↦
    (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
      (joined_pasted_newEdge profile distinguished)).trans
      (wall_block_eq_double_block input profile hSheet)
  genus_eq := joined_sourceGenus profile distinguished

noncomputable def joinedLiftData (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    LiftData data wall where
  toBackgroundShape := joinedBackgroundShape input profile distinguished
  valid := input.valid
  selected_valency_ne_two := selected_valency_ne_two profile

/-- **`M⁽³⁾`'s selected `t₂` endpoint is its branch vertex**, so it is never
divalent. -/
theorem joined_old_valency_ne_two (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    nonDanglingValency (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).datum.sourceEndpoint
        (oldVertex target wall) sheet) ≠ 2 := by
  rw [joined_nonDanglingValency_old input shape distinguished sheet hRel]
  omega

/-- **The surviving pair at `M⁽³⁾`'s selected `t₃` endpoint**: the retained `e₃`
and the one regrown occurrence. -/
theorem joined_selected_right_pair (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    ∃ other : Fin degree, (data.vertexPartition wall).Rel block.1 other ∧
      nonDanglingIncident (joinedCandidate profile distinguished).datum
          ((joinedCandidate profile distinguished).datum.sourceEndpoint
            (freshVertex target) sheet) =
        {(joinedCandidate profile distinguished).newSourceEdge other,
          (joinedCandidate profile distinguished).oldSourceEdge profile.third.1} := by
  refine ⟨sheet, hRel, ?_⟩
  rw [joined_nonDanglingIncident_fresh input shape distinguished sheet hRel]
  exact Finset.pair_comm _ _

/-- The `A₀` half of `W2MkkStableGraph`'s joined census, read as the core's
selected data.  Every selected sheet's regrown occurrence represents `e₃`. -/
noncomputable def joinedSelectedData (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) : SelectedData data wall where
  toLiftData := joinedLiftData input profile distinguished
  selectedRep := fun _ ↦ profile.third.1
  selectedRep_survives := fun _ _ ↦ profile.third_survives
  selectedRep_congr := fun _ _ _ _ _ ↦ rfl
  selected_new_stablePath := fun sheet hRel _ _ ↦
    joined_new_stablePath_eq_third input shape distinguished sheet hRel
  selected_left_pair := fun sheet hRel hValency ↦
    absurd hValency (joined_old_valency_ne_two input shape distinguished sheet hRel)
  selected_right_pair := fun sheet hRel _ ↦
    joined_selected_right_pair input shape distinguished sheet hRel

@[simp] theorem joinedSelectedData_candidate (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedSelectedData input shape distinguished).candidate =
      joinedCandidate profile distinguished := rfl

@[simp] theorem joinedSelectedData_selected (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedSelectedData input shape distinguished).selected = block.1 := rfl

@[simp] theorem joinedSelectedData_selectedRep (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished sheet : Fin degree) :
    (joinedSelectedData input shape distinguished).selectedRep sheet = profile.third.1 := rfl

@[simp] theorem joinedSelectedData_retainedTarget (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    (joinedSelectedData input shape distinguished).retainedTarget =
      star.edge profile.doubleLabel := rfl

/-! ## The stable lifts -/

/-- **Figure 34's induced stable-row map for a detaching member**, evaluated by
retaining any actual surviving occurrence of the old row. -/
noncomputable def detachStablePathLift (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    StablePath data → StablePath (detach.candidate shape).datum :=
  (detachLiftData input shape detach).stablePathLift

@[simp] theorem detachStablePathLift_mk (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (edge : NonDanglingEdge data) :
    detachStablePathLift input shape detach edge.stablePath =
      (retainedEdge (detach.candidate shape) input.valid.1 edge).stablePath := rfl

/-- Retaining a different occurrence of one old stable row gives the same row
upstairs. -/
theorem detach_stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (detach.candidate shape) input.valid.1 first).stablePath =
      (retainedEdge (detach.candidate shape) input.valid.1 second).stablePath :=
  (detachLiftData input shape detach).retained_stablePath_eq_of_consecutive first second
    hConsecutive

/-- No stable row of a detaching member lies entirely in the new fibre. -/
theorem detach_exists_retained_row (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (edge : NonDanglingEdge (detach.candidate shape).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (detach.candidate shape) input.valid.1 old).stablePath = edge.stablePath :=
  (detachSelectedData input shape detach).exists_retained_row edge

theorem detach_stablePathLift_surjective (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    Function.Surjective (detachStablePathLift input shape detach) :=
  (detachSelectedData input shape detach).stablePathLift_surjective

/-- **Figure 34's induced stable-row map for `M⁽³⁾`.** -/
noncomputable def joinedStablePathLift (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree) :
    StablePath data → StablePath (joinedCandidate profile distinguished).datum :=
  (joinedLiftData input profile distinguished).stablePathLift

@[simp] theorem joinedStablePathLift_mk (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree)
    (edge : NonDanglingEdge data) :
    joinedStablePathLift input profile distinguished edge.stablePath =
      (retainedEdge (joinedCandidate profile distinguished) input.valid.1 edge).stablePath := rfl

theorem joined_stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block) (distinguished : Fin degree)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (joinedCandidate profile distinguished) input.valid.1 first).stablePath =
      (retainedEdge (joinedCandidate profile distinguished) input.valid.1 second).stablePath :=
  (joinedLiftData input profile distinguished).retained_stablePath_eq_of_consecutive first second
    hConsecutive

theorem joined_exists_retained_row (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree)
    (edge : NonDanglingEdge (joinedCandidate profile distinguished).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (joinedCandidate profile distinguished) input.valid.1 old).stablePath =
        edge.stablePath :=
  (joinedSelectedData input shape distinguished).exists_retained_row edge

theorem joined_stablePathLift_surjective (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    Function.Surjective (joinedStablePathLift input profile distinguished) :=
  (joinedSelectedData input shape distinguished).stablePathLift_surjective

end DraismaVargas.LocalCases.W2MkkStableLift
