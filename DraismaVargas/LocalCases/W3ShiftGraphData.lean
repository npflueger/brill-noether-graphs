module

public import DraismaVargas.LocalCases.W3ShiftLimitRows
public import DraismaVargas.LocalCases.LimitChainCore

@[expose] public section

/-!
# Figure 29's two members as `LimitChainCore` instances

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a>k4)} (the `w3Shift`
case), its Positions II.a and II.b, Figure 29 and Equation (3).

## What this file settles

The geometric half of the honest-matrix step for Equation (3): for **each**
member of Equation (3)'s
pair, the occurrence-induced stable-row equivalence `stablePathEquiv`, the
retained columns `matrix_retained`, and the stable incidence graph
`equivalence`; and, composed through the incoming datum's own stable graph, the
`StableGraphIncidence.Equivalence` **between** the two members
(`shrinkToGrow` / `growToShrink`, and their `Fin 2`-indexed form `between`).

`W3ShiftLimitRows` derives `W3ShiftClosure.LimitRows` at **one fixed** labelling,
out of `W3FourStableGraph.gaugePresentation`, whose regrown row assignment
(`ShiftMemberColumn.selectedSheets`) is *supplied*; nothing there says a
presented matrix is the member's own `StableSourceMatrix.matrix`.  This module
supplies exactly that missing layer, by instantiating the generic limit-matrix
chain `LimitChainCore` twice.  `W3ShiftHonestBalance` then re-derives
`W3ShiftClosure.LimitRows` at an *arbitrary* labelling on top of it.

## Why the core had to be instantiated afresh, member by member

`W3FourRowDescent.GrowMember` looks like it should cover Figure 29's grow member
-- the two have the same local shape, `fineResolution` of an enlarged class at
the divalent endpoint over the distinguished block and the moving direction's
own fine star everywhere else -- but it **cannot**: it is stated for a
`W3FourSourceCandidates.GrowProfile`, whose field
`largest_index : k₄ = |A₀|` is exactly the `(a = k₄)` selector that this case
negates (`ShiftProfile.moving_lt` gives `k_α < |A₀|` for every direction).  No
`GrowProfile` exists on a shift datum, so neither `W3FourSurvival.GrowMember`
nor anything stated over `W3FourClosure.FourStarGeometry` applies.  The same
obstruction is why `W3ShiftLimitRows` restates
`W3FourStableGraph.MemberColumn` with the bare anchor.  Figure 29's shrink
member is not a Figure 28 shape at all: its selected block carries
`ResolutionMkk.bothDetachedResolution`, which is neither `fineResolution` nor
its reverse.

**The core itself fits both members on every field.**  Nothing below is
supplied: `LimitChainCore.GraphData` is constructed outright for each.

## The shape of the instantiation

* `MemberData` -- what the two members share: `right = rightOf t_α` and
  `resolution = onBlock … selectedResolution (t_α's fine star)`, with the single
  local resolution they differ in as a field.  Both instances are `rfl`
  (`growMember`, `shrinkMember`).  Everything generic -- the pasted endpoint
  dictionary above and away from the distinguished block, the core's
  `BackgroundShape` (`coreShape`), and the two endpoint classifications
  `incident_old_cases` / `incident_fresh_cases` -- is proved once on it.
* `SelectedCensus` -- the census at the distinguished block, in the shape both
  members satisfy: one surviving regrown class `main` meeting the retained `e_α`
  at a divalent retained endpoint, every other regrown class pruned, and one
  fresh endpoint `branch` carrying that occurrence with `e_β` and `e_γ`.
  `SelectedCensus.graphData` assembles `LimitChainCore.GraphData` from it, once.
* `Grow.census` and `Shrink.census` -- the two instances.  Both take
  `branch := shrink.remainder`, so the two members' background columns are
  literally the same function, which is what makes Equation (3)'s crossed column
  identity in `W3ShiftHonestBalance` a `ring` step.

## The two members' selected-block censuses, in words

**Position II.a** (`Grow`).  Over `A₀` the retained endpoint splits along
`growPartition`: the enlarged class `e_α ∪ {x}` and singletons.  At that
enlarged class the surviving star is the regrown occurrence of index `k_α + 1`
together with the retained `e_α` (`Grow.old_main`); every other regrown class
dangles and its endpoint is entirely pruned
(`Grow.new_dangles_of_separate`, `Grow.old_empty`).  The fresh endpoint carries
the whole wall block, and is the branch vertex (`Grow.fresh_branch`).

**Position II.b** (`Shrink`).  The retained endpoint is `e_α` itself; the new
edge and the fresh endpoint each lose the transferred sheet `x`.  The regrown
singleton through `x` dangles, because its fresh endpoint is the detached
singleton class and the two retained directions avoid `x`
(`Shrink.new_transfer_dangles`, from `ShrinkData.transfer_not_first` /
`transfer_not_second`); the residual regrown class, of index `k_α − 1`, meets
`e_α` at the divalent retained endpoint (`Shrink.old_main`); and the residual
fresh endpoint is the branch vertex (`Shrink.fresh_branch`).  So the shrink
member's branch vertex is named by `remainder`, not by `movingAnchor` -- the
`ShrinkData` fields do not forbid `transfer = movingAnchor`, and taking
`movingAnchor` would name the pruned singleton endpoint instead.

## What is not proved here

No determinant, no balance, no incoming-member identification, and no branch
swap: `W3ShiftClosure.exists_gauge_shift_pair` performs both swaps first, so
every member below lives over one datum and the identity gauge is the only one
used.  The regrown column's *value* is `W3ShiftHonestBalance`'s.
-/

namespace DraismaVargas.LocalCases.W3ShiftGraphData

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount
open W3R1SourceProfile
open W3ShiftSourceCandidates
open LimitChainCore (wallSide)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The incoming selected star -/

/-- Any sheet of a wall block names that block's quotient-source vertex. -/
theorem sourceEndpoint_eq_wallBlock (block : WallBlock data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    data.sourceEndpoint wall sheet = WallBlock.sourceVertex data wall block :=
  Subtype.ext (Prod.ext rfl hSheet.symm)

theorem firstRest_survives (shift : ShiftProfile input) :
    ¬ IsDangling data shift.firstRest.1 :=
  (mem_survivors data input.distinguishedBlock shift.firstRest).mp
    (by rw [shift.surviving]; simp)

theorem secondRest_survives (shift : ShiftProfile input) :
    ¬ IsDangling data shift.secondRest.1 :=
  (mem_survivors data input.distinguishedBlock shift.secondRest).mp
    (by rw [shift.surviving]; simp)

theorem moving_self (shift : ShiftProfile input) :
    data.sourceEdge shift.movingTarget shift.movingAnchor = shift.moving.1 :=
  GluingDatum.sourceEdge_self data shift.moving.1

theorem firstRest_self (shift : ShiftProfile input) :
    data.sourceEdge shift.firstTarget shift.firstAnchor = shift.firstRest.1 :=
  GluingDatum.sourceEdge_self data shift.firstRest.1

theorem secondRest_self (shift : ShiftProfile input) :
    data.sourceEdge shift.secondTarget shift.secondAnchor = shift.secondRest.1 :=
  GluingDatum.sourceEdge_self data shift.secondRest.1

/-- **The incoming census at the distinguished block**: the three actual
survivors exhaust it. -/
theorem selected_exhaustive (shift : ShiftProfile input) (edge : data.SourceEdge)
    (hIncident : Incident data edge (data.sourceEndpoint wall shift.movingAnchor))
    (hSurvives : ¬ IsDangling data edge) :
    edge = shift.moving.1 ∨ edge = shift.firstRest.1 ∨ edge = shift.secondRest.1 := by
  classical
  rw [sourceEndpoint_eq_wallBlock input.distinguishedBlock shift.movingAnchor
    shift.movingAnchor_wall_rel] at hIncident
  have hMem := (mem_survivors data input.distinguishedBlock
    ⟨edge, hIncident⟩).mpr hSurvives
  rw [shift.surviving] at hMem
  rcases Finset.mem_insert.mp hMem with hEq | hRest
  · exact Or.inl (congrArg Subtype.val hEq)
  · rcases Finset.mem_insert.mp hRest with hEq | hEq
    · exact Or.inr (Or.inl (congrArg Subtype.val hEq))
    · exact Or.inr (Or.inr (congrArg Subtype.val (Finset.mem_singleton.mp hEq)))

theorem firstAnchor_wall_rel' (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel shift.movingAnchor shift.firstAnchor :=
  shift.movingAnchor_wall_rel.symm.trans shift.firstAnchor_wall_rel

theorem secondAnchor_wall_rel' (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel shift.movingAnchor shift.secondAnchor :=
  shift.movingAnchor_wall_rel.symm.trans shift.secondAnchor_wall_rel

/-- The complete surviving star at the distinguished source vertex. -/
theorem selected_nonDanglingIncident (shift : ShiftProfile input) :
    nonDanglingIncident data (data.sourceEndpoint wall shift.movingAnchor) =
      {shift.moving.1, shift.firstRest.1, shift.secondRest.1} := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases selected_exhaustive shift edge hIncident hSurvives with h | h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr h))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨W3ShiftLimitRows.moving_survives shift, ?_⟩
      rw [← moving_self shift]
      exact incident_sourceEdge_sourceEndpoint data wall shift.movingTarget
        shift.movingTarget_mem shift.movingAnchor
    · rcases Finset.mem_insert.mp hRest with rfl | hLast
      · refine (mem_nonDanglingIncident _ _ _).mpr ⟨firstRest_survives shift, ?_⟩
        rw [LimitChainCore.sourceEndpoint_eq_of_rel data wall
          (firstAnchor_wall_rel' shift), ← firstRest_self shift]
        exact incident_sourceEdge_sourceEndpoint data wall shift.firstTarget
          shift.firstTarget_mem shift.firstAnchor
      · rw [Finset.mem_singleton.mp hLast]
        refine (mem_nonDanglingIncident _ _ _).mpr ⟨secondRest_survives shift, ?_⟩
        rw [LimitChainCore.sourceEndpoint_eq_of_rel data wall
          (secondAnchor_wall_rel' shift), ← secondRest_self shift]
        exact incident_sourceEdge_sourceEndpoint data wall shift.secondTarget
          shift.secondTarget_mem shift.secondAnchor

theorem moving_ne_firstRest (shift : ShiftProfile input) :
    shift.moving.1 ≠ shift.firstRest.1 := by
  intro h
  exact shift.moving_target_ne_first (congrArg (fun e : data.SourceEdge ↦ e.1.1) h)

theorem moving_ne_secondRest (shift : ShiftProfile input) :
    shift.moving.1 ≠ shift.secondRest.1 := by
  intro h
  exact shift.moving_target_ne_second (congrArg (fun e : data.SourceEdge ↦ e.1.1) h)

theorem firstRest_ne_secondRest (shift : ShiftProfile input) :
    shift.firstRest.1 ≠ shift.secondRest.1 := by
  intro h
  exact shift.first_target_ne_second (congrArg (fun e : data.SourceEdge ↦ e.1.1) h)

/-- **The distinguished source vertex is trivalent.** -/
theorem selected_nonDanglingValency_eq_three (shift : ShiftProfile input)
    {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    nonDanglingValency data (data.sourceEndpoint wall sheet) = 3 := by
  classical
  rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall hSheet,
    ← card_nonDanglingIncident, selected_nonDanglingIncident shift]
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨moving_ne_firstRest shift, moving_ne_secondRest shift⟩),
    Finset.card_pair (firstRest_ne_secondRest shift)]

theorem selected_nonDanglingValency_ne_two (shift : ShiftProfile input)
    {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    nonDanglingValency data (data.sourceEndpoint wall sheet) ≠ 2 := by
  rw [selected_nonDanglingValency_eq_three shift hSheet]
  decide


/-! ## The common shape of Figure 29's two members

Both members install the moving direction's own fine star on every background
wall block and differ only in the local resolution they put on the
distinguished one.  `MemberData` names that difference, and everything below
is proved once for an arbitrary `MemberData`. -/

/-- Everything Figure 29's two members share, with the one local resolution
they differ in as a field. -/
structure MemberData (shift : ShiftProfile input) where
  /-- The local resolution installed on the distinguished wall block. -/
  selectedResolution : LocalResolution degree
  /-- The globally assembled member. -/
  candidate : Candidate target degree data wall
  /-- The moving direction sits alone at the retained endpoint. -/
  right_eq : candidate.right = W3Nd2SourceCandidates.rightOf shift.movingTarget
  /-- and the member is the moving direction's fine star off the distinguished
  block. -/
  resolution_eq : candidate.resolution =
    LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
      selectedResolution
      (fun _ ↦ fineResolution (data.vertexPartition wall)
        (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
  /-- It preserves the source genus. -/
  genus_eq : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace MemberData

variable {shift : ShiftProfile input} (m : MemberData shift)

theorem right_moving : m.candidate.right shift.movingTarget = false := by
  rw [m.right_eq]
  simp [W3Nd2SourceCandidates.rightOf]

theorem right_of_ne {edge : target.edges} (hNe : edge ≠ shift.movingTarget) :
    m.candidate.right edge = true := by
  rw [m.right_eq]
  simp [W3Nd2SourceCandidates.rightOf, hNe]

theorem right_first : m.candidate.right shift.firstTarget = true :=
  m.right_of_ne (Ne.symm shift.moving_target_ne_first)

theorem right_second : m.candidate.right shift.secondTarget = true :=
  m.right_of_ne (Ne.symm shift.moving_target_ne_second)

theorem eq_moving_of_right_false {edge : target.edges}
    (hRight : m.candidate.right edge = false) : edge = shift.movingTarget := by
  by_contra hNe
  rw [m.right_of_ne hNe] at hRight
  exact Bool.noConfusion hRight

/-- The pasted local resolution of the member. -/
noncomputable abbrev pasted : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall) m.candidate.resolution
    m.candidate.contracts

theorem resolution_selected {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.candidate.resolution sheet = m.selectedResolution := by
  rw [m.resolution_eq, LocalResolution.onBlock_of_rel _ _ _ _ _ hSheet]

theorem resolution_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.candidate.resolution sheet =
      fineResolution (data.vertexPartition wall)
        (data.edgePartition shift.movingTarget) shift.movingTarget_refines := by
  rw [m.resolution_eq, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSheet]

/-! ### The pasted endpoint dictionary above the distinguished block -/

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.left.block sheet = m.selectedResolution.left.block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]

theorem pasted_right_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.right.block sheet = m.selectedResolution.right.block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.newEdge.block sheet = m.selectedResolution.newEdge.block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]

theorem pasted_left_rel_iff {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    (sheet : Fin degree) :
    m.pasted.left.Rel anchor sheet ↔ m.selectedResolution.left.Rel anchor sheet := by
  constructor
  · intro hRel
    have hMem : sheet ∈ m.pasted.left.block anchor :=
      (m.pasted.left.mem_block_iff anchor sheet).mpr hRel
    rw [m.pasted_left_block hAnchor] at hMem
    exact (m.selectedResolution.left.mem_block_iff anchor sheet).mp hMem
  · intro hRel
    have hMem : sheet ∈ m.selectedResolution.left.block anchor :=
      (m.selectedResolution.left.mem_block_iff anchor sheet).mpr hRel
    rw [← m.pasted_left_block hAnchor] at hMem
    exact (m.pasted.left.mem_block_iff anchor sheet).mp hMem

theorem pasted_right_rel_iff {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    (sheet : Fin degree) :
    m.pasted.right.Rel anchor sheet ↔ m.selectedResolution.right.Rel anchor sheet := by
  constructor
  · intro hRel
    have hMem : sheet ∈ m.pasted.right.block anchor :=
      (m.pasted.right.mem_block_iff anchor sheet).mpr hRel
    rw [m.pasted_right_block hAnchor] at hMem
    exact (m.selectedResolution.right.mem_block_iff anchor sheet).mp hMem
  · intro hRel
    have hMem : sheet ∈ m.selectedResolution.right.block anchor :=
      (m.selectedResolution.right.mem_block_iff anchor sheet).mpr hRel
    rw [← m.pasted_right_block hAnchor] at hMem
    exact (m.pasted.right.mem_block_iff anchor sheet).mp hMem

theorem pasted_newEdge_rel_iff {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    (sheet : Fin degree) :
    m.pasted.newEdge.Rel anchor sheet ↔
      m.selectedResolution.newEdge.Rel anchor sheet := by
  constructor
  · intro hRel
    have hMem : sheet ∈ m.pasted.newEdge.block anchor :=
      (m.pasted.newEdge.mem_block_iff anchor sheet).mpr hRel
    rw [m.pasted_newEdge_block hAnchor] at hMem
    exact (m.selectedResolution.newEdge.mem_block_iff anchor sheet).mp hMem
  · intro hRel
    have hMem : sheet ∈ m.selectedResolution.newEdge.block anchor :=
      (m.selectedResolution.newEdge.mem_block_iff anchor sheet).mpr hRel
    rw [← m.pasted_newEdge_block hAnchor] at hMem
    exact (m.pasted.newEdge.mem_block_iff anchor sheet).mp hMem

end MemberData


/-! ## The background half, and the core's `BackgroundShape` -/

namespace MemberData

variable {shift : ShiftProfile input} (m : MemberData shift)

theorem pasted_left_block_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.left.block sheet =
      (data.edgePartition shift.movingTarget).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_background (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem pasted_right_block_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.right.block sheet = (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_background (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem pasted_newEdge_block_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    m.pasted.newEdge.block sheet =
      (data.edgePartition shift.movingTarget).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    m.candidate.resolution m.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [m.resolution_background (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

/-- **A Figure 29 member, read as the core's `BackgroundShape`**, with the
distinguished block named by any one of its sheets. -/
noncomputable def coreShape {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor) :
    LimitChainCore.BackgroundShape data wall where
  candidate := m.candidate
  retainedTarget := shift.movingTarget
  target_mem := shift.movingTarget_mem
  left := m.right_moving
  unique := fun _ _ hRight ↦ m.eq_moving_of_right_false hRight
  selected := anchor
  left_block := fun hSheet ↦
    m.pasted_left_block_background (fun hRel ↦ hSheet (hAnchor.symm.trans hRel))
  right_block := fun hSheet ↦
    m.pasted_right_block_background (fun hRel ↦ hSheet (hAnchor.symm.trans hRel))
  newEdge_block := fun hSheet ↦
    m.pasted_newEdge_block_background (fun hRel ↦ hSheet (hAnchor.symm.trans hRel))
  genus_eq := m.genus_eq

@[simp] theorem coreShape_candidate {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor) :
    (m.coreShape hAnchor).candidate = m.candidate := rfl

@[simp] theorem coreShape_selected {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor) :
    (m.coreShape hAnchor).selected = anchor := rfl

@[simp] theorem coreShape_retainedTarget {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor) :
    (m.coreShape hAnchor).retainedTarget = shift.movingTarget := rfl

/-! ### Occurrences and incidences -/

theorem old_isDangling_iff (hValid : data.Valid) (edge : data.SourceEdge) :
    IsDangling m.candidate.datum (m.candidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff m.candidate hValid m.genus_eq edge

theorem new_ne_old (sheet : Fin degree) (edge : data.SourceEdge) :
    m.candidate.newSourceEdge sheet ≠ m.candidate.oldSourceEdge edge :=
  fun h ↦ LimitChainCore.oldSourceEdge_ne_newSourceEdge edge sheet h.symm

theorem new_incident_old (sheet : Fin degree) :
    Incident m.candidate.datum (m.candidate.newSourceEdge sheet)
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  LimitChainCore.newSourceEdge_incident_old sheet

theorem new_incident_fresh (sheet : Fin degree) :
    Incident m.candidate.datum (m.candidate.newSourceEdge sheet)
      (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  LimitChainCore.newSourceEdge_incident_fresh sheet

theorem moving_incident_old (sheet : Fin degree) :
    Incident m.candidate.datum
        (m.candidate.oldSourceEdge (data.sourceEdge shift.movingTarget sheet))
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  LimitChainCore.oldSourceEdge_incident_old m.candidate shift.movingTarget
    shift.movingTarget_mem m.right_moving sheet

theorem first_incident_fresh (sheet : Fin degree) :
    Incident m.candidate.datum
        (m.candidate.oldSourceEdge (data.sourceEdge shift.firstTarget sheet))
      (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh m.candidate shift.firstTarget
    shift.firstTarget_mem m.right_first sheet

theorem second_incident_fresh (sheet : Fin degree) :
    Incident m.candidate.datum
        (m.candidate.oldSourceEdge (data.sourceEdge shift.secondTarget sheet))
      (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh m.candidate shift.secondTarget
    shift.secondTarget_mem m.right_second sheet

theorem old_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel shift.movingAnchor first)
    (hRel : m.selectedResolution.left.Rel first second) :
    m.candidate.datum.sourceEndpoint (oldVertex target wall) first =
      m.candidate.datum.sourceEndpoint (oldVertex target wall) second :=
  LimitChainCore.sourceEndpoint_old_eq_of_rel first second
    ((m.pasted_left_rel_iff hFirst second).mpr hRel)

theorem fresh_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel shift.movingAnchor first)
    (hRel : m.selectedResolution.right.Rel first second) :
    m.candidate.datum.sourceEndpoint (freshVertex target) first =
      m.candidate.datum.sourceEndpoint (freshVertex target) second :=
  LimitChainCore.sourceEndpoint_fresh_eq_of_rel first second
    ((m.pasted_right_rel_iff hFirst second).mpr hRel)

theorem newSourceEdge_eq_of_rel {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel shift.movingAnchor first)
    (hRel : m.selectedResolution.newEdge.Rel first second) :
    m.candidate.newSourceEdge second = m.candidate.newSourceEdge first :=
  ((LimitChainCore.newSourceEdge_eq_iff_rel first second).mpr
    ((m.pasted_newEdge_rel_iff hFirst second).mpr hRel)).symm

theorem moving_survives_out (hValid : data.Valid) :
    ¬ IsDangling m.candidate.datum (m.candidate.oldSourceEdge shift.moving.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge m.candidate hValid.1 _
    (W3ShiftLimitRows.moving_survives shift)

theorem first_survives_out (hValid : data.Valid) :
    ¬ IsDangling m.candidate.datum (m.candidate.oldSourceEdge shift.firstRest.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge m.candidate hValid.1 _
    (firstRest_survives shift)

theorem second_survives_out (hValid : data.Valid) :
    ¬ IsDangling m.candidate.datum (m.candidate.oldSourceEdge shift.secondRest.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge m.candidate hValid.1 _
    (secondRest_survives shift)

theorem old_first_ne_second :
    m.candidate.oldSourceEdge shift.firstRest.1 ≠
      m.candidate.oldSourceEdge shift.secondRest.1 := fun hEq ↦
  firstRest_ne_secondRest shift (ResolutionCut.oldSourceEdge_injective m.candidate hEq)

theorem old_moving_ne_first :
    m.candidate.oldSourceEdge shift.moving.1 ≠
      m.candidate.oldSourceEdge shift.firstRest.1 := fun hEq ↦
  moving_ne_firstRest shift (ResolutionCut.oldSourceEdge_injective m.candidate hEq)

end MemberData


/-! ## The two endpoint classifications above the distinguished block -/

namespace MemberData

variable {shift : ShiftProfile input} (m : MemberData shift)

theorem selectedResolution_contracts :
    m.selectedResolution.ContractsTo (data.vertexPartition wall) := by
  have hContracts := m.candidate.contracts shift.movingAnchor
  rwa [m.resolution_selected
    (show (data.vertexPartition wall).Rel shift.movingAnchor shift.movingAnchor
      from rfl)] at hContracts

theorem left_refines : m.selectedResolution.left.Refines (data.vertexPartition wall) :=
  m.selectedResolution_contracts.left_refines

theorem right_refines : m.selectedResolution.right.Refines (data.vertexPartition wall) :=
  m.selectedResolution_contracts.right_refines

theorem newEdge_refines :
    m.selectedResolution.newEdge.Refines (data.vertexPartition wall) :=
  m.selectedResolution.edge_refines_left.trans m.left_refines

theorem selectedBlock_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (data.vertexPartition wall).Rel
      (WallBlock.ofSheet data wall shift.movingAnchor).1 sheet :=
  ((data.vertexPartition wall).rel_repr_left shift.movingAnchor).trans hSheet

theorem sourceVertex_selectedBlock :
    WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall shift.movingAnchor) =
      data.sourceEndpoint wall shift.movingAnchor :=
  LimitChainCore.sourceVertex_ofSheet data wall shift.movingAnchor

/-- **The retained endpoint above the distinguished block.**  Only the moving
direction is present there, and `e_α` is its only survivor. -/
theorem incident_old_cases (hValid : data.Valid) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    {edge : m.candidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling m.candidate.datum edge)
    (hIncident : Incident m.candidate.datum edge
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    (∃ sheet : Fin degree, m.selectedResolution.left.Rel anchor sheet ∧
        edge = m.candidate.newSourceEdge sheet) ∨
      (edge = m.candidate.oldSourceEdge shift.moving.1 ∧
        m.selectedResolution.left.Rel anchor shift.movingAnchor) := by
  rcases ResolutionPruning.sourceEdge_cases m.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · obtain ⟨hData, hRight⟩ := LimitChainCore.old_incident_old_selected_info
      m.candidate (WallBlock.ofSheet data wall shift.movingAnchor) anchor
      (selectedBlock_rel hAnchor) old hIncident
    rw [sourceVertex_selectedBlock (shift := shift)] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((m.old_isDangling_iff hValid old).mpr hDangling)
    have hSheetRel : m.selectedResolution.left.Rel anchor old.1.2 :=
      (m.pasted_left_rel_iff hAnchor old.1.2).mp
        (LimitChainCore.old_incident_old_sheet_rel m.candidate anchor old hIncident)
    rcases selected_exhaustive shift old hData hOldSurvives with rfl | rfl | rfl
    · exact Or.inr ⟨rfl, hSheetRel⟩
    · exact Bool.noConfusion (m.right_first.symm.trans hRight)
    · exact Bool.noConfusion (m.right_second.symm.trans hRight)
  · refine Or.inl ⟨m.pasted.newEdge.repr new, ?_, ?_⟩
    · exact (m.pasted_left_rel_iff hAnchor _).mp
        (LimitChainCore.new_incident_old_sheet_rel m.candidate anchor new hIncident)
    · exact (LimitChainCore.newSourceEdge_repr m.candidate new).symm

/-- **The fresh endpoint above the distinguished block.**  The two retained
directions are present there, with survivors `e_β`, `e_γ`; every other survivor
is one of the member's own regrown occurrences. -/
theorem incident_fresh_cases (hValid : data.Valid) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel shift.movingAnchor anchor)
    {edge : m.candidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling m.candidate.datum edge)
    (hIncident : Incident m.candidate.datum edge
      (m.candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (∃ sheet : Fin degree, m.selectedResolution.right.Rel anchor sheet ∧
        edge = m.candidate.newSourceEdge sheet) ∨
      (edge = m.candidate.oldSourceEdge shift.firstRest.1 ∧
        m.selectedResolution.right.Rel anchor shift.firstAnchor) ∨
      (edge = m.candidate.oldSourceEdge shift.secondRest.1 ∧
        m.selectedResolution.right.Rel anchor shift.secondAnchor) := by
  rcases ResolutionPruning.sourceEdge_cases m.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · obtain ⟨hData, hRight⟩ := LimitChainCore.old_incident_fresh_selected_info
      m.candidate (WallBlock.ofSheet data wall shift.movingAnchor) anchor
      (selectedBlock_rel hAnchor) old hIncident
    rw [sourceVertex_selectedBlock (shift := shift)] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((m.old_isDangling_iff hValid old).mpr hDangling)
    have hSheetRel : m.selectedResolution.right.Rel anchor old.1.2 :=
      (m.pasted_right_rel_iff hAnchor old.1.2).mp
        (LimitChainCore.old_incident_fresh_sheet_rel m.candidate anchor old hIncident)
    rcases selected_exhaustive shift old hData hOldSurvives with rfl | rfl | rfl
    · exact Bool.noConfusion (m.right_moving.symm.trans hRight)
    · exact Or.inr (Or.inl ⟨rfl, hSheetRel⟩)
    · exact Or.inr (Or.inr ⟨rfl, hSheetRel⟩)
  · refine Or.inl ⟨m.pasted.newEdge.repr new, ?_, ?_⟩
    · refine (m.pasted_right_rel_iff hAnchor _).mp ?_
      have hOutgoing := (incident_iff_target_mem_and_rel m.candidate.datum
        (m.candidate.newSourceEdge new)
        (m.candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
      change occurrenceEquiv target wall m.candidate.right none ∈
          GluingDatum.incidentEdges (freshVertex target) ∧
        m.pasted.right.Rel (m.pasted.right.repr anchor)
          (m.pasted.newEdge.repr new) at hOutgoing
      exact (m.pasted.right.rel_repr_right anchor).trans hOutgoing.2
    · exact (LimitChainCore.newSourceEdge_repr m.candidate new).symm

end MemberData


/-! ## The selected-block census both members satisfy

Figure 29's two members differ at the distinguished wall block, but the shape
of their census there is the same: one surviving regrown occurrence `main`
meeting the retained `e_α` at a divalent retained endpoint, every other
regrown class pruned, and one fresh endpoint `branch` carrying that occurrence
together with the two retained survivors `e_β`, `e_γ`.  `SelectedCensus` names
that shape, and the core's `GraphData` is assembled from it once. -/

structure SelectedCensus {shift : ShiftProfile input} (m : MemberData shift) where
  /-- The sheet carrying the member's surviving regrown occurrence. -/
  main : Fin degree
  main_wall : (data.vertexPartition wall).Rel shift.movingAnchor main
  /-- The sheet naming the member's branch vertex above the distinguished
  block. -/
  branch : Fin degree
  branch_wall : (data.vertexPartition wall).Rel shift.movingAnchor branch
  /-- `e_α` ends at the retained endpoint of the main regrown class. -/
  left_main : m.selectedResolution.left.Rel main shift.movingAnchor
  /-- Every other regrown class above the distinguished block is pruned. -/
  new_dangles : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel shift.movingAnchor sheet →
    ¬ m.selectedResolution.newEdge.Rel sheet main →
      IsDangling m.candidate.datum (m.candidate.newSourceEdge sheet)
  /-- and every other retained endpoint above it is entirely pruned. -/
  old_empty : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel shift.movingAnchor sheet →
    ¬ m.selectedResolution.left.Rel sheet main →
      nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = ∅
  /-- The retained endpoint of the main class is divalent. -/
  old_main : nonDanglingIncident m.candidate.datum
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) main) =
    {m.candidate.newSourceEdge main, m.candidate.oldSourceEdge shift.moving.1}
  /-- The branch vertex carries the regrown occurrence and `e_β`, `e_γ`. -/
  fresh_branch : nonDanglingIncident m.candidate.datum
      (m.candidate.datum.sourceEndpoint (freshVertex target) branch) =
    {m.candidate.newSourceEdge main, m.candidate.oldSourceEdge shift.firstRest.1,
      m.candidate.oldSourceEdge shift.secondRest.1}
  /-- Every other fresh endpoint above the distinguished block is pruned. -/
  fresh_empty : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel shift.movingAnchor sheet →
    m.candidate.datum.sourceEndpoint (freshVertex target) sheet ≠
      m.candidate.datum.sourceEndpoint (freshVertex target) branch →
      nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) = ∅

namespace SelectedCensus

variable {shift : ShiftProfile input} {m : MemberData shift} (c : SelectedCensus m)

/-- The member's regrown occurrence survives. -/
theorem new_main_survives :
    ¬ IsDangling m.candidate.datum (m.candidate.newSourceEdge c.main) := by
  have hMem : m.candidate.newSourceEdge c.main ∈
      nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (oldVertex target wall) c.main) := by
    rw [c.old_main]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

theorem old_main_valency :
    nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) c.main) = 2 := by
  classical
  rw [← card_nonDanglingIncident, c.old_main]
  exact Finset.card_pair (m.new_ne_old _ _)

theorem moving_incident_main :
    Incident m.candidate.datum (m.candidate.oldSourceEdge shift.moving.1)
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) c.main) := by
  have hIncident := m.moving_incident_old shift.movingAnchor
  rw [moving_self shift] at hIncident
  rw [m.old_endpoint_eq c.main_wall c.left_main]
  exact hIncident

/-- **The regrown occurrence lies in `e_α`'s stable row.** -/
theorem new_main_stablePath (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨m.candidate.newSourceEdge c.main, c.new_main_survives⟩ :
          NonDanglingEdge m.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨m.candidate.oldSourceEdge shift.moving.1, m.moving_survives_out hValid⟩ :
          NonDanglingEdge m.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, m.new_incident_old c.main,
    c.moving_incident_main, c.old_main_valency⟩
  intro hEq
  exact m.new_ne_old c.main _ (congrArg Subtype.val hEq)

theorem new_ne_first :
    m.candidate.newSourceEdge c.main ≠ m.candidate.oldSourceEdge shift.firstRest.1 :=
  m.new_ne_old _ _

theorem new_ne_second :
    m.candidate.newSourceEdge c.main ≠ m.candidate.oldSourceEdge shift.secondRest.1 :=
  m.new_ne_old _ _

theorem fresh_branch_valency :
    nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (freshVertex target) c.branch) = 3 := by
  classical
  rw [← card_nonDanglingIncident, c.fresh_branch,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨c.new_ne_first, c.new_ne_second⟩),
    Finset.card_pair m.old_first_ne_second]

/-! ### The flag dictionary at the branch vertex -/

/-- The branch flag: the regrown occurrence replaces `e_α`, and `e_β`, `e_γ`
are retained. -/
noncomputable def flag (edge : data.SourceEdge) : m.candidate.datum.SourceEdge :=
  if edge.1.1 = shift.movingTarget then m.candidate.newSourceEdge c.main
  else m.candidate.oldSourceEdge edge

theorem flag_moving : c.flag shift.moving.1 = m.candidate.newSourceEdge c.main :=
  ite_eq_left rfl

theorem flag_of_ne {edge : data.SourceEdge} (hNe : edge.1.1 ≠ shift.movingTarget) :
    c.flag edge = m.candidate.oldSourceEdge edge := ite_eq_right hNe

theorem flag_first :
    c.flag shift.firstRest.1 = m.candidate.oldSourceEdge shift.firstRest.1 :=
  c.flag_of_ne (Ne.symm shift.moving_target_ne_first)

theorem flag_second :
    c.flag shift.secondRest.1 = m.candidate.oldSourceEdge shift.secondRest.1 :=
  c.flag_of_ne (Ne.symm shift.moving_target_ne_second)

theorem incoming_branch_star :
    nonDanglingIncident data (data.sourceEndpoint wall c.branch) =
      {shift.moving.1, shift.firstRest.1, shift.secondRest.1} := by
  rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall c.branch_wall]
  exact selected_nonDanglingIncident shift

theorem flag_star :
    nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (wallSide target wall true) c.branch) =
      (nonDanglingIncident data (data.sourceEndpoint wall c.branch)).image c.flag := by
  classical
  rw [LimitChainCore.wallSide_true, c.fresh_branch, c.incoming_branch_star,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    c.flag_moving, c.flag_first, c.flag_second]

theorem flag_injOn :
    Set.InjOn c.flag ↑(nonDanglingIncident data (data.sourceEndpoint wall c.branch)) := by
  classical
  apply Finset.injOn_of_card_image_eq
  rw [← c.flag_star, card_nonDanglingIncident, card_nonDanglingIncident]
  show nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (freshVertex target) c.branch) =
    nonDanglingValency data (data.sourceEndpoint wall c.branch)
  rw [c.fresh_branch_valency,
    selected_nonDanglingValency_eq_three shift c.branch_wall]

theorem flag_row (hValid : data.Valid) (edge : data.SourceEdge)
    (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall c.branch))
    (hFlag : ¬ IsDangling m.candidate.datum (c.flag edge)) :
    NonDanglingEdge.stablePath
        (⟨c.flag edge, hFlag⟩ : NonDanglingEdge m.candidate.datum) =
      (ResolutionAwayFromWall.retainedEdge m.candidate hValid.1
        ⟨edge, hSurvives⟩).stablePath := by
  rw [← LimitChainCore.sourceEndpoint_eq_of_rel data wall c.branch_wall] at hIncident
  rcases selected_exhaustive shift edge hIncident hSurvives with rfl | rfl | rfl
  · refine Eq.trans (congrArg NonDanglingEdge.stablePath
      (show (⟨c.flag shift.moving.1, hFlag⟩ : NonDanglingEdge m.candidate.datum) =
          ⟨m.candidate.newSourceEdge c.main, c.new_main_survives⟩
        from Subtype.ext c.flag_moving)) ?_
    exact c.new_main_stablePath hValid
  · exact congrArg NonDanglingEdge.stablePath (Subtype.ext c.flag_first)
  · exact congrArg NonDanglingEdge.stablePath (Subtype.ext c.flag_second)

end SelectedCensus


/-! ### The core's `GraphData`, assembled from a selected census -/

namespace SelectedCensus

variable {shift : ShiftProfile input} {m : MemberData shift} (c : SelectedCensus m)

theorem old_star_of_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hRel : m.selectedResolution.left.Rel sheet c.main) :
    nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {m.candidate.newSourceEdge c.main, m.candidate.oldSourceEdge shift.moving.1} := by
  rw [m.old_endpoint_eq hSheet hRel]
  exact c.old_main

theorem old_valency_le_two (c : SelectedCensus m) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ≤ 2 := by
  classical
  by_cases hRel : m.selectedResolution.left.Rel sheet c.main
  · rw [← card_nonDanglingIncident, c.old_star_of_rel hSheet hRel]
    exact le_of_eq (Finset.card_pair (m.new_ne_old _ _))
  · rw [← card_nonDanglingIncident, c.old_empty sheet hSheet hRel, Finset.card_empty]
    omega

theorem old_star_of_valency_two {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hValency : nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2) :
    nonDanglingIncident m.candidate.datum
        (m.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {m.candidate.newSourceEdge c.main, m.candidate.oldSourceEdge shift.moving.1} := by
  classical
  by_cases hRel : m.selectedResolution.left.Rel sheet c.main
  · exact c.old_star_of_rel hSheet hRel
  · rw [← card_nonDanglingIncident, c.old_empty sheet hSheet hRel,
      Finset.card_empty] at hValency
    exact absurd hValency (by decide)

theorem fresh_valency_ne_two (c : SelectedCensus m) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) ≠ 2 := by
  classical
  by_cases hVertex : m.candidate.datum.sourceEndpoint (freshVertex target) sheet =
      m.candidate.datum.sourceEndpoint (freshVertex target) c.branch
  · rw [hVertex, c.fresh_branch_valency]
    decide
  · rw [← card_nonDanglingIncident, c.fresh_empty sheet hSheet hVertex,
      Finset.card_empty]
    decide

theorem fresh_valency_le_two_of_ne {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hVertex : m.candidate.datum.sourceEndpoint (freshVertex target) sheet ≠
      m.candidate.datum.sourceEndpoint (freshVertex target) c.branch) :
    nonDanglingValency m.candidate.datum
      (m.candidate.datum.sourceEndpoint (freshVertex target) sheet) ≤ 2 := by
  classical
  rw [← card_nonDanglingIncident, c.fresh_empty sheet hSheet hVertex,
    Finset.card_empty]
  omega

/-- **A Figure 29 member, packaged for the generic limit-matrix chain.** -/
noncomputable def graphData (hValid : data.Valid) :
    LimitChainCore.GraphData data wall where
  toBackgroundShape := m.coreShape c.branch_wall
  valid := hValid
  selected_valency_ne_two :=
    selected_nonDanglingValency_ne_two shift c.branch_wall
  selectedRep := fun _ ↦ shift.moving.1
  selectedRep_survives := fun _ _ ↦ W3ShiftLimitRows.moving_survives shift
  selectedRep_congr := fun _ _ _ _ _ ↦ rfl
  selected_new_stablePath := by
    intro sheet hSheet hSurvives _
    have hWall : (data.vertexPartition wall).Rel shift.movingAnchor sheet :=
      c.branch_wall.trans hSheet
    by_cases hRel : m.selectedResolution.newEdge.Rel sheet c.main
    · refine Eq.trans (congrArg NonDanglingEdge.stablePath
        (show (⟨m.candidate.newSourceEdge sheet, hSurvives⟩ :
              NonDanglingEdge m.candidate.datum) =
            ⟨m.candidate.newSourceEdge c.main, c.new_main_survives⟩
          from Subtype.ext (m.newSourceEdge_eq_of_rel hWall hRel).symm)) ?_
      exact c.new_main_stablePath hValid
    · exact absurd (c.new_dangles sheet hWall hRel) hSurvives
  selected_left_pair := by
    intro sheet hSheet hValency
    exact ⟨c.main, c.branch_wall.symm.trans c.main_wall,
      c.old_star_of_valency_two (c.branch_wall.trans hSheet) hValency⟩
  selected_right_pair := by
    intro sheet hSheet hValency
    exact (c.fresh_valency_ne_two (c.branch_wall.trans hSheet) hValency).elim
  selectedSide := true
  selectedFlag := c.flag
  selectedFlag_star := c.flag_star
  selectedFlag_injOn := c.flag_injOn
  selected_not_branch := by
    intro side sheet hSheet hNe
    cases side with
    | false =>
        simp only [LimitChainCore.wallSide_false]
        exact c.old_valency_le_two (c.branch_wall.trans hSheet)
    | true =>
        simp only [LimitChainCore.wallSide_true] at hNe ⊢
        exact c.fresh_valency_le_two_of_ne (c.branch_wall.trans hSheet) hNe
  selectedFlag_row := fun edge hSurvives hIncident hFlag ↦
    c.flag_row hValid edge hSurvives hIncident hFlag

@[simp] theorem graphData_candidate (hValid : data.Valid) :
    (c.graphData hValid).candidate = m.candidate := rfl

end SelectedCensus


/-! ## Figure 29's grow member (Position II.a) -/

namespace MemberData

variable {shift : ShiftProfile input} (m : MemberData shift)

theorem candidate_valid (hValid : data.Valid) : m.candidate.datum.Valid :=
  m.candidate.datum_valid hValid

end MemberData

/-- Figure 29's Position II.a member, in the common shape. -/
noncomputable def growMember (shift : ShiftProfile input) : MemberData shift where
  selectedResolution := fineResolution (data.vertexPartition wall)
    shift.growPartition shift.growPartition_refines
  candidate := shift.growCandidate
  right_eq := rfl
  resolution_eq := rfl
  genus_eq := shift.growCandidate_sourceGenus

@[simp] theorem growMember_candidate (shift : ShiftProfile input) :
    (growMember shift).candidate = shift.growCandidate := rfl

theorem growMember_left (shift : ShiftProfile input) :
    (growMember shift).selectedResolution.left = shift.growPartition := rfl

theorem growMember_right (shift : ShiftProfile input) :
    (growMember shift).selectedResolution.right = data.vertexPartition wall := rfl

theorem growMember_newEdge (shift : ShiftProfile input) :
    (growMember shift).selectedResolution.newEdge = shift.growPartition := rfl

namespace Grow

variable (shift : ShiftProfile input)

/-- **Every regrown class of the grow member outside the enlarged one is
pruned.**  Its retained endpoint is a singleton class of `growPartition`, and
the only old occurrence there is a dangling singleton class of `e_α`. -/
theorem new_dangles_of_separate (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hSep : ¬ shift.growPartition.Rel sheet shift.movingAnchor) :
    IsDangling (growMember shift).candidate.datum
      ((growMember shift).candidate.newSourceEdge sheet) := by
  classical
  by_contra hSurvives
  have hSubset : nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ⊆
      {(growMember shift).candidate.newSourceEdge sheet} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (growMember shift).incident_old_cases hValid hSheet hEdgeSurvives
      hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩
    · exact Finset.mem_singleton.mpr
        ((growMember shift).newSourceEdge_eq_of_rel hSheet hRel)
    · exact absurd hRel hSep
  have hLe := (Finset.card_le_card hSubset).trans_eq (Finset.card_singleton _)
  have hPos : 0 < (nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvives, (growMember shift).new_incident_old sheet⟩⟩
  have hNe : (nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one _
      ((growMember shift).candidate_valid hValid).1 _
  omega

/-- Those retained endpoints are entirely pruned. -/
theorem old_empty (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hSep : ¬ shift.growPartition.Rel sheet shift.movingAnchor) :
    nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge hMem
  obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases (growMember shift).incident_old_cases hValid hSheet hEdgeSurvives
    hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩
  · refine hEdgeSurvives ?_
    rw [(growMember shift).newSourceEdge_eq_of_rel hSheet hRel]
    exact new_dangles_of_separate shift hValid hSheet hSep
  · exact hSep hRel

/-- **The divalent retained endpoint of the grow member.** -/
theorem old_main (hValid : data.Valid) :
    nonDanglingIncident (growMember shift).candidate.datum
        ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
          shift.movingAnchor) =
      {(growMember shift).candidate.newSourceEdge shift.movingAnchor,
        (growMember shift).candidate.oldSourceEdge shift.moving.1} := by
  classical
  have hSubset : nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        shift.movingAnchor) ⊆
      {(growMember shift).candidate.newSourceEdge shift.movingAnchor,
        (growMember shift).candidate.oldSourceEdge shift.moving.1} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (growMember shift).incident_old_cases hValid
      (show (data.vertexPartition wall).Rel shift.movingAnchor shift.movingAnchor
        from rfl) hEdgeSurvives hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨hOld, _⟩
    · exact Finset.mem_insert.mpr (Or.inl
        ((growMember shift).newSourceEdge_eq_of_rel rfl hRel))
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)
  have hPairCard : ({(growMember shift).candidate.newSourceEdge shift.movingAnchor,
      (growMember shift).candidate.oldSourceEdge shift.moving.1} :
      Finset (growMember shift).candidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair ((growMember shift).new_ne_old _ _)
  have hIncidentMoving :
      Incident (growMember shift).candidate.datum
        ((growMember shift).candidate.oldSourceEdge shift.moving.1)
        ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
          shift.movingAnchor) := by
    have h := (growMember shift).moving_incident_old shift.movingAnchor
    rwa [moving_self shift] at h
  have hPos : 0 < (nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        shift.movingAnchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨(growMember shift).moving_survives_out hValid, hIncidentMoving⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident (growMember shift).candidate.datum
      ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
        shift.movingAnchor)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one _
      ((growMember shift).candidate_valid hValid).1 _
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

theorem new_main_survives (hValid : data.Valid) :
    ¬ IsDangling (growMember shift).candidate.datum
      ((growMember shift).candidate.newSourceEdge shift.movingAnchor) := by
  have hMem : (growMember shift).candidate.newSourceEdge shift.movingAnchor ∈
      nonDanglingIncident (growMember shift).candidate.datum
        ((growMember shift).candidate.datum.sourceEndpoint (oldVertex target wall)
          shift.movingAnchor) := by
    rw [old_main shift hValid]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-- **The trivalent fresh endpoint of the grow member is its branch vertex.** -/
theorem fresh_branch (hValid : data.Valid) {branch : Fin degree}
    (hBranch : (data.vertexPartition wall).Rel shift.movingAnchor branch) :
    nonDanglingIncident (growMember shift).candidate.datum
        ((growMember shift).candidate.datum.sourceEndpoint (freshVertex target)
          branch) =
      {(growMember shift).candidate.newSourceEdge shift.movingAnchor,
        (growMember shift).candidate.oldSourceEdge shift.firstRest.1,
        (growMember shift).candidate.oldSourceEdge shift.secondRest.1} := by
  classical
  have hFreshMoving : (growMember shift).candidate.datum.sourceEndpoint
      (freshVertex target) branch =
      (growMember shift).candidate.datum.sourceEndpoint (freshVertex target)
        shift.movingAnchor :=
    (growMember shift).fresh_endpoint_eq hBranch hBranch.symm
  have hFreshFirst : (growMember shift).candidate.datum.sourceEndpoint
      (freshVertex target) branch =
      (growMember shift).candidate.datum.sourceEndpoint (freshVertex target)
        shift.firstAnchor :=
    (growMember shift).fresh_endpoint_eq hBranch
      (hBranch.symm.trans (firstAnchor_wall_rel' shift))
  have hFreshSecond : (growMember shift).candidate.datum.sourceEndpoint
      (freshVertex target) branch =
      (growMember shift).candidate.datum.sourceEndpoint (freshVertex target)
        shift.secondAnchor :=
    (growMember shift).fresh_endpoint_eq hBranch
      (hBranch.symm.trans (secondAnchor_wall_rel' shift))
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (growMember shift).incident_fresh_cases hValid hBranch hEdgeSurvives
      hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨hFirst, _⟩ | ⟨hSecond, _⟩
    · have hWall : (data.vertexPartition wall).Rel shift.movingAnchor other :=
        hBranch.trans hRel
      refine Finset.mem_insert.mpr (Or.inl ?_)
      by_cases hGrow : shift.growPartition.Rel other shift.movingAnchor
      · exact (growMember shift).newSourceEdge_eq_of_rel
          (show (data.vertexPartition wall).Rel shift.movingAnchor
            shift.movingAnchor from rfl) hGrow.symm
      · exact absurd (new_dangles_of_separate shift hValid hWall hGrow) hEdgeSurvives
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hFirst))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hSecond))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · refine (mem_nonDanglingIncident _ _ _).mpr ⟨new_main_survives shift hValid, ?_⟩
      rw [hFreshMoving]
      exact (growMember shift).new_incident_fresh shift.movingAnchor
    · rcases Finset.mem_insert.mp hRest with rfl | hLast
      · refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨(growMember shift).first_survives_out hValid, ?_⟩
        rw [hFreshFirst, ← firstRest_self shift]
        exact (growMember shift).first_incident_fresh shift.firstAnchor
      · rw [Finset.mem_singleton.mp hLast]
        refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨(growMember shift).second_survives_out hValid, ?_⟩
        rw [hFreshSecond, ← secondRest_self shift]
        exact (growMember shift).second_incident_fresh shift.secondAnchor

/-- **The grow member's selected census.** -/
noncomputable def census (hValid : data.Valid) {branch : Fin degree}
    (hBranch : (data.vertexPartition wall).Rel shift.movingAnchor branch) :
    SelectedCensus (growMember shift) where
  main := shift.movingAnchor
  main_wall := rfl
  branch := branch
  branch_wall := hBranch
  left_main := rfl
  new_dangles := fun sheet hSheet hRel ↦
    new_dangles_of_separate shift hValid hSheet hRel
  old_empty := fun sheet hSheet hRel ↦ old_empty shift hValid hSheet hRel
  old_main := old_main shift hValid
  fresh_branch := fresh_branch shift hValid hBranch
  fresh_empty := by
    intro sheet hSheet hVertex
    exact absurd ((growMember shift).fresh_endpoint_eq hSheet
      (hSheet.symm.trans hBranch)) hVertex

end Grow


/-! ## Figure 29's shrink member (Position II.b) -/

/-- Figure 29's Position II.b member, in the common shape. -/
noncomputable def shrinkMember {shift : ShiftProfile input} (shrink : ShrinkData shift) :
    MemberData shift where
  selectedResolution := shrink.selected
  candidate := shrink.shrinkCandidate
  right_eq := rfl
  resolution_eq := rfl
  genus_eq := shrink.shrinkCandidate_sourceGenus

@[simp] theorem shrinkMember_candidate {shift : ShiftProfile input}
    (shrink : ShrinkData shift) :
    (shrinkMember shrink).candidate = shrink.shrinkCandidate := rfl

namespace Shrink

variable {shift : ShiftProfile input} (shrink : ShrinkData shift)

theorem left_eq :
    (shrinkMember shrink).selectedResolution.left =
      data.edgePartition shift.movingTarget := rfl

theorem right_eq :
    (shrinkMember shrink).selectedResolution.right =
      (data.vertexPartition wall).detachSheet shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_wall_rel := rfl

theorem newEdge_eq :
    (shrinkMember shrink).selectedResolution.newEdge =
      (data.edgePartition shift.movingTarget).detachSheet shrink.transfer
        shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving := rfl

theorem moving_rel_remainder :
    (data.edgePartition shift.movingTarget).Rel shift.movingAnchor shrink.remainder :=
  shrink.transfer_moving.trans shrink.remainder_moving

theorem wall_rel_transfer :
    (data.vertexPartition wall).Rel shift.movingAnchor shrink.transfer :=
  shift.movingAnchor_wall_rel.symm.trans shrink.transfer_wall_rel

theorem wall_rel_remainder :
    (data.vertexPartition wall).Rel shift.movingAnchor shrink.remainder :=
  shift.movingTarget_refines.rel (moving_rel_remainder shrink)

theorem wall_rel_transfer_of_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (data.vertexPartition wall).Rel shrink.transfer sheet :=
  (wall_rel_transfer shrink).symm.trans hSheet

theorem firstAnchor_ne_transfer : shift.firstAnchor ≠ shrink.transfer := by
  intro hEq
  exact shrink.transfer_not_first (hEq ▸ rfl)

theorem secondAnchor_ne_transfer : shift.secondAnchor ≠ shrink.transfer := by
  intro hEq
  exact shrink.transfer_not_second (hEq ▸ rfl)

theorem right_rel_transfer_iff (sheet : Fin degree) :
    (shrinkMember shrink).selectedResolution.right.Rel shrink.transfer sheet ↔
      shrink.transfer = sheet :=
  (data.vertexPartition wall).detachSheet_rel_single_iff shrink.transfer
    shrink.remainder sheet shrink.transfer_ne_remainder shrink.remainder_wall_rel

theorem newEdge_rel_transfer_iff (sheet : Fin degree) :
    (shrinkMember shrink).selectedResolution.newEdge.Rel shrink.transfer sheet ↔
      shrink.transfer = sheet :=
  (data.edgePartition shift.movingTarget).detachSheet_rel_single_iff shrink.transfer
    shrink.remainder sheet shrink.transfer_ne_remainder shrink.remainder_moving

theorem newEdge_rel_remainder_iff (sheet : Fin degree) :
    (shrinkMember shrink).selectedResolution.newEdge.Rel shrink.remainder sheet ↔
      (sheet ≠ shrink.transfer ∧
        (data.edgePartition shift.movingTarget).Rel shrink.transfer sheet) := by
  classical
  have hBlock := (data.edgePartition shift.movingTarget).detachSheet_block_remainder
    shrink.transfer shrink.remainder shrink.transfer_ne_remainder
    shrink.remainder_moving
  constructor
  · intro hRel
    have hMem : sheet ∈ ((data.edgePartition shift.movingTarget).detachSheet
        shrink.transfer shrink.remainder shrink.transfer_ne_remainder
        shrink.remainder_moving).block shrink.remainder :=
      (((data.edgePartition shift.movingTarget).detachSheet shrink.transfer
        shrink.remainder shrink.transfer_ne_remainder
        shrink.remainder_moving).mem_block_iff shrink.remainder sheet).mpr hRel
    rw [hBlock, Finset.mem_erase] at hMem
    exact ⟨hMem.1,
      ((data.edgePartition shift.movingTarget).mem_block_iff shrink.transfer
        sheet).mp hMem.2⟩
  · rintro ⟨hNe, hRel⟩
    have hMem : sheet ∈ ((data.edgePartition shift.movingTarget).detachSheet
        shrink.transfer shrink.remainder shrink.transfer_ne_remainder
        shrink.remainder_moving).block shrink.remainder := by
      rw [hBlock, Finset.mem_erase]
      exact ⟨hNe, ((data.edgePartition shift.movingTarget).mem_block_iff
        shrink.transfer sheet).mpr hRel⟩
    exact (((data.edgePartition shift.movingTarget).detachSheet shrink.transfer
      shrink.remainder shrink.transfer_ne_remainder
      shrink.remainder_moving).mem_block_iff shrink.remainder sheet).mp hMem

theorem right_rel_remainder {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hNe : sheet ≠ shrink.transfer) :
    (shrinkMember shrink).selectedResolution.right.Rel sheet shrink.remainder :=
  W3ShiftSourceCandidates.detachSheet_rel_remainder (data.vertexPartition wall)
    shrink.transfer shrink.remainder sheet shrink.transfer_ne_remainder
    shrink.remainder_wall_rel (wall_rel_transfer_of_rel shrink hSheet) hNe

/-- **Position II.b's detached regrown singleton is pruned.**  Its fresh
endpoint is the detached singleton class of the trivalent endpoint, and the two
retained directions avoid the transferred sheet. -/
theorem new_transfer_dangles (hValid : data.Valid) :
    IsDangling (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.newSourceEdge shrink.transfer) := by
  classical
  by_contra hSurvives
  have hSubset : nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shrink.transfer) ⊆
      {(shrinkMember shrink).candidate.newSourceEdge shrink.transfer} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (shrinkMember shrink).incident_fresh_cases hValid
      (wall_rel_transfer shrink) hEdgeSurvives hEdgeIncident with
      ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩ | ⟨_, hRel⟩
    · refine Finset.mem_singleton.mpr ?_
      rw [(right_rel_transfer_iff shrink other).mp hRel]
    · exact absurd (((right_rel_transfer_iff shrink shift.firstAnchor).mp hRel).symm)
        (firstAnchor_ne_transfer shrink)
    · exact absurd (((right_rel_transfer_iff shrink shift.secondAnchor).mp hRel).symm)
        (secondAnchor_ne_transfer shrink)
  have hLe := (Finset.card_le_card hSubset).trans_eq (Finset.card_singleton _)
  have hPos : 0 < (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shrink.transfer)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvives, (shrinkMember shrink).new_incident_fresh shrink.transfer⟩⟩
  have hNe : (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shrink.transfer)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one _
      ((shrinkMember shrink).candidate_valid hValid).1 _
  omega

/-- Off `e_α` the retained endpoints of Position II.b are singletons, so their
regrown occurrences are pruned too. -/
theorem new_outside_dangles (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hSep : ¬ (data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet) :
    IsDangling (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.newSourceEdge sheet) := by
  classical
  have hSingleton : (data.edgePartition shift.movingTarget).block sheet = {sheet} :=
    SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
      (moving_blockCard_eq_one shift sheet
        (shift.movingAnchor_wall_rel.trans hSheet) hSep)
  by_contra hSurvives
  have hSubset : nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet) ⊆
      {(shrinkMember shrink).candidate.newSourceEdge sheet} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (shrinkMember shrink).incident_old_cases hValid hSheet hEdgeSurvives
      hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩
    · have hMemOther : other ∈ (data.edgePartition shift.movingTarget).block sheet :=
        ((data.edgePartition shift.movingTarget).mem_block_iff sheet other).mpr hRel
      rw [hSingleton, Finset.mem_singleton] at hMemOther
      exact Finset.mem_singleton.mpr (by rw [hMemOther])
    · exact absurd hRel.symm hSep
  have hLe := (Finset.card_le_card hSubset).trans_eq (Finset.card_singleton _)
  have hPos : 0 < (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvives, (shrinkMember shrink).new_incident_old sheet⟩⟩
  have hNe : (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one _
      ((shrinkMember shrink).candidate_valid hValid).1 _
  omega

theorem new_dangles (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hSep : ¬ (shrinkMember shrink).selectedResolution.newEdge.Rel sheet
      shrink.remainder) :
    IsDangling (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.newSourceEdge sheet) := by
  by_cases hMoving : (data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet
  · have hTransferRel : (data.edgePartition shift.movingTarget).Rel shrink.transfer
        sheet := shrink.transfer_moving.symm.trans hMoving
    by_cases hNe : sheet = shrink.transfer
    · rw [hNe]
      exact new_transfer_dangles shrink hValid
    · exact absurd (((newEdge_rel_remainder_iff shrink sheet).mpr
        ⟨hNe, hTransferRel⟩).symm) hSep
  · exact new_outside_dangles shrink hValid hSheet hMoving

theorem old_empty (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hSep : ¬ (shrinkMember shrink).selectedResolution.left.Rel sheet
      shrink.remainder) :
    nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        sheet) = ∅ := by
  classical
  have hMoving : ¬ (data.edgePartition shift.movingTarget).Rel shift.movingAnchor
      sheet := fun hRel ↦ hSep (hRel.symm.trans (moving_rel_remainder shrink))
  have hSingleton : (data.edgePartition shift.movingTarget).block sheet = {sheet} :=
    SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
      (moving_blockCard_eq_one shift sheet
        (shift.movingAnchor_wall_rel.trans hSheet) hMoving)
  apply Finset.eq_empty_of_forall_notMem
  intro edge hMem
  obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases (shrinkMember shrink).incident_old_cases hValid hSheet hEdgeSurvives
    hEdgeIncident with ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩
  · have hMemOther : other ∈ (data.edgePartition shift.movingTarget).block sheet :=
      ((data.edgePartition shift.movingTarget).mem_block_iff sheet other).mpr hRel
    rw [hSingleton, Finset.mem_singleton] at hMemOther
    refine hEdgeSurvives ?_
    rw [hMemOther]
    exact new_outside_dangles shrink hValid hSheet hMoving
  · exact absurd hRel.symm hMoving

end Shrink


namespace Shrink

variable {shift : ShiftProfile input} (shrink : ShrinkData shift)

theorem fresh_transfer_empty (hValid : data.Valid) :
    nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shrink.transfer) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge hMem
  obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases (shrinkMember shrink).incident_fresh_cases hValid
    (wall_rel_transfer shrink) hEdgeSurvives hEdgeIncident with
    ⟨other, hRel, rfl⟩ | ⟨_, hRel⟩ | ⟨_, hRel⟩
  · refine hEdgeSurvives ?_
    rw [← (right_rel_transfer_iff shrink other).mp hRel]
    exact new_transfer_dangles shrink hValid
  · exact absurd (((right_rel_transfer_iff shrink shift.firstAnchor).mp hRel).symm)
      (firstAnchor_ne_transfer shrink)
  · exact absurd (((right_rel_transfer_iff shrink shift.secondAnchor).mp hRel).symm)
      (secondAnchor_ne_transfer shrink)

theorem old_endpoint_remainder :
    (shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        shrink.remainder =
      (shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        shift.movingAnchor :=
  (shrinkMember shrink).old_endpoint_eq (wall_rel_remainder shrink)
    (moving_rel_remainder shrink).symm

/-- **Position II.b's divalent retained endpoint above `e_α`.** -/
theorem old_main (hValid : data.Valid) :
    nonDanglingIncident (shrinkMember shrink).candidate.datum
        ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
          shrink.remainder) =
      {(shrinkMember shrink).candidate.newSourceEdge shrink.remainder,
        (shrinkMember shrink).candidate.oldSourceEdge shift.moving.1} := by
  classical
  have hSubset : nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        shrink.remainder) ⊆
      {(shrinkMember shrink).candidate.newSourceEdge shrink.remainder,
        (shrinkMember shrink).candidate.oldSourceEdge shift.moving.1} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (shrinkMember shrink).incident_old_cases hValid
      (wall_rel_remainder shrink) hEdgeSurvives hEdgeIncident with
      ⟨other, hRel, rfl⟩ | ⟨hOld, _⟩
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      have hTransferRel : (data.edgePartition shift.movingTarget).Rel shrink.transfer
          other := shrink.remainder_moving.trans hRel
      by_cases hNe : other = shrink.transfer
      · refine absurd ?_ hEdgeSurvives
        rw [hNe]
        exact new_transfer_dangles shrink hValid
      · exact (shrinkMember shrink).newSourceEdge_eq_of_rel (wall_rel_remainder shrink)
          ((newEdge_rel_remainder_iff shrink other).mpr ⟨hNe, hTransferRel⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)
  have hPairCard : ({(shrinkMember shrink).candidate.newSourceEdge shrink.remainder,
      (shrinkMember shrink).candidate.oldSourceEdge shift.moving.1} :
      Finset (shrinkMember shrink).candidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair ((shrinkMember shrink).new_ne_old _ _)
  have hIncidentMoving :
      Incident (shrinkMember shrink).candidate.datum
        ((shrinkMember shrink).candidate.oldSourceEdge shift.moving.1)
        ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
          shrink.remainder) := by
    rw [old_endpoint_remainder shrink]
    have h := (shrinkMember shrink).moving_incident_old shift.movingAnchor
    rwa [moving_self shift] at h
  have hPos : 0 < (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        shrink.remainder)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨(shrinkMember shrink).moving_survives_out hValid, hIncidentMoving⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
        shrink.remainder)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one _
      ((shrinkMember shrink).candidate_valid hValid).1 _
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

theorem new_main_survives (hValid : data.Valid) :
    ¬ IsDangling (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.newSourceEdge shrink.remainder) := by
  have hMem : (shrinkMember shrink).candidate.newSourceEdge shrink.remainder ∈
      nonDanglingIncident (shrinkMember shrink).candidate.datum
        ((shrinkMember shrink).candidate.datum.sourceEndpoint (oldVertex target wall)
          shrink.remainder) := by
    rw [old_main shrink hValid]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-- **Position II.b's trivalent fresh endpoint is its branch vertex.** -/
theorem fresh_branch (hValid : data.Valid) :
    nonDanglingIncident (shrinkMember shrink).candidate.datum
        ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
          shrink.remainder) =
      {(shrinkMember shrink).candidate.newSourceEdge shrink.remainder,
        (shrinkMember shrink).candidate.oldSourceEdge shift.firstRest.1,
        (shrinkMember shrink).candidate.oldSourceEdge shift.secondRest.1} := by
  classical
  have hFreshFirst : (shrinkMember shrink).candidate.datum.sourceEndpoint
      (freshVertex target) shrink.remainder =
      (shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shift.firstAnchor :=
    (shrinkMember shrink).fresh_endpoint_eq (wall_rel_remainder shrink)
      ((right_rel_remainder shrink (firstAnchor_wall_rel' shift)
        (firstAnchor_ne_transfer shrink)).symm)
  have hFreshSecond : (shrinkMember shrink).candidate.datum.sourceEndpoint
      (freshVertex target) shrink.remainder =
      (shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shift.secondAnchor :=
    (shrinkMember shrink).fresh_endpoint_eq (wall_rel_remainder shrink)
      ((right_rel_remainder shrink (secondAnchor_wall_rel' shift)
        (secondAnchor_ne_transfer shrink)).symm)
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases (shrinkMember shrink).incident_fresh_cases hValid
      (wall_rel_remainder shrink) hEdgeSurvives hEdgeIncident with
      ⟨other, hRel, rfl⟩ | ⟨hFirst, _⟩ | ⟨hSecond, _⟩
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      have hWallOther : (data.vertexPartition wall).Rel shift.movingAnchor other :=
        (wall_rel_remainder shrink).trans ((shrinkMember shrink).right_refines.rel hRel)
      have hOtherNe : other ≠ shrink.transfer := by
        intro hEq
        subst hEq
        exact shrink.transfer_ne_remainder
          ((right_rel_transfer_iff shrink shrink.remainder).mp hRel.symm)
      by_cases hMoving : (data.edgePartition shift.movingTarget).Rel shift.movingAnchor
          other
      · exact (shrinkMember shrink).newSourceEdge_eq_of_rel (wall_rel_remainder shrink)
          ((newEdge_rel_remainder_iff shrink other).mpr
            ⟨hOtherNe, shrink.transfer_moving.symm.trans hMoving⟩)
      · exact absurd (new_outside_dangles shrink hValid hWallOther hMoving)
          hEdgeSurvives
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hFirst))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hSecond))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨new_main_survives shrink hValid,
        (shrinkMember shrink).new_incident_fresh shrink.remainder⟩
    · rcases Finset.mem_insert.mp hRest with rfl | hLast
      · refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨(shrinkMember shrink).first_survives_out hValid, ?_⟩
        rw [hFreshFirst, ← firstRest_self shift]
        exact (shrinkMember shrink).first_incident_fresh shift.firstAnchor
      · rw [Finset.mem_singleton.mp hLast]
        refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨(shrinkMember shrink).second_survives_out hValid, ?_⟩
        rw [hFreshSecond, ← secondRest_self shift]
        exact (shrinkMember shrink).second_incident_fresh shift.secondAnchor

theorem fresh_empty (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel shift.movingAnchor sheet)
    (hVertex : (shrinkMember shrink).candidate.datum.sourceEndpoint
        (freshVertex target) sheet ≠
      (shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        shrink.remainder) :
    nonDanglingIncident (shrinkMember shrink).candidate.datum
      ((shrinkMember shrink).candidate.datum.sourceEndpoint (freshVertex target)
        sheet) = ∅ := by
  by_cases hNe : sheet = shrink.transfer
  · subst hNe
    exact fresh_transfer_empty shrink hValid
  · exact absurd ((shrinkMember shrink).fresh_endpoint_eq hSheet
      (right_rel_remainder shrink hSheet hNe)) hVertex

/-- **The shrink member's selected census.** -/
noncomputable def census (hValid : data.Valid) :
    SelectedCensus (shrinkMember shrink) where
  main := shrink.remainder
  main_wall := wall_rel_remainder shrink
  branch := shrink.remainder
  branch_wall := wall_rel_remainder shrink
  left_main := (moving_rel_remainder shrink).symm
  new_dangles := fun _ hSheet hRel ↦ new_dangles shrink hValid hSheet hRel
  old_empty := fun _ hSheet hRel ↦ old_empty shrink hValid hSheet hRel
  old_main := old_main shrink hValid
  fresh_branch := fresh_branch shrink hValid
  fresh_empty := fun _ hSheet hVertex ↦ fresh_empty shrink hValid hSheet hVertex

end Shrink


/-! ## The pair's row equivalences, retained columns and stable incidence graphs -/

section Pair

variable {shift : ShiftProfile input} (shrink : ShrinkData shift) (hValid : data.Valid)

/-- Position II.b, packaged for the generic limit-matrix chain. -/
noncomputable def shrinkRowData : LimitChainCore.GraphData data wall :=
  (Shrink.census shrink hValid).graphData hValid

/-- Position II.a, packaged for the generic limit-matrix chain. -/
noncomputable def growRowData : LimitChainCore.GraphData data wall :=
  (Grow.census shift hValid (Shrink.wall_rel_remainder shrink)).graphData hValid

@[simp] theorem shrinkRowData_candidate :
    (shrinkRowData shrink hValid).candidate = shrink.shrinkCandidate := rfl

@[simp] theorem growRowData_candidate :
    (growRowData shrink hValid).candidate = shift.growCandidate := rfl

/-- **Position II.b's occurrence-induced stable-row equivalence.** -/
noncomputable def shrinkStablePathEquiv :
    StablePath data ≃ StablePath shrink.shrinkCandidate.datum :=
  (shrinkRowData shrink hValid).stablePathEquiv

/-- **Position II.a's occurrence-induced stable-row equivalence.** -/
noncomputable def growStablePathEquiv :
    StablePath data ≃ StablePath shift.growCandidate.datum :=
  (growRowData shrink hValid).stablePathEquiv

/-- **Every retained column of Position II.b is the incoming wall column.** -/
theorem shrink_matrix_retained (path : StablePath data) (place : target.edges) :
    matrix shrink.shrinkCandidate.datum
        (shrinkStablePathEquiv shrink hValid path)
        (occurrenceEquiv target wall shrink.shrinkCandidate.right (some place)) =
      matrix data path place :=
  (shrinkRowData shrink hValid).matrix_retained path place

/-- **Every retained column of Position II.a is the incoming wall column.** -/
theorem grow_matrix_retained (path : StablePath data) (place : target.edges) :
    matrix shift.growCandidate.datum
        (growStablePathEquiv shrink hValid path)
        (occurrenceEquiv target wall shift.growCandidate.right (some place)) =
      matrix data path place :=
  (growRowData shrink hValid).matrix_retained path place

/-- **Position II.b's stable incidence graph is the incoming one.** -/
noncomputable def shrinkEquivalence :
    StableGraphIncidence.Equivalence data shrink.shrinkCandidate.datum :=
  (shrinkRowData shrink hValid).equivalence

/-- **Position II.a's stable incidence graph is the incoming one.** -/
noncomputable def growEquivalence :
    StableGraphIncidence.Equivalence data shift.growCandidate.datum :=
  (growRowData shrink hValid).equivalence

@[simp] theorem shrinkEquivalence_row :
    (shrinkEquivalence shrink hValid).row = shrinkStablePathEquiv shrink hValid := rfl

@[simp] theorem growEquivalence_row :
    (growEquivalence shrink hValid).row = growStablePathEquiv shrink hValid := rfl

/-! ### The pair, indexed as `W3ShiftLimitRows.shiftMembers` -/

/-- The occurrence-induced row equivalence of member `i` of Equation (3)'s
pair. -/
noncomputable def rowEquiv (i : Fin 2) :
    StablePath data ≃ StablePath (W3ShiftLimitRows.shiftMembers shrink i).datum :=
  Fin.cases (shrinkStablePathEquiv shrink hValid)
    (Fin.cases (growStablePathEquiv shrink hValid) (fun i ↦ i.elim0)) i

/-- **Each member of Equation (3)'s pair carries the incoming stable incidence
graph.** -/
noncomputable def memberEquivalence (i : Fin 2) :
    StableGraphIncidence.Equivalence data
      (W3ShiftLimitRows.shiftMembers shrink i).datum :=
  Fin.cases (shrinkEquivalence shrink hValid)
    (Fin.cases (growEquivalence shrink hValid) (fun i ↦ i.elim0)) i

theorem memberEquivalence_row (i : Fin 2) :
    (memberEquivalence shrink hValid i).row = rowEquiv shrink hValid i := by
  fin_cases i <;> rfl

/-- **The stable-incidence dictionary between the two members of Equation (3)'s
pair**, composed through the incoming datum's own stable graph.  The incoming
datum is never the transport source: both members carry it, and `between` is
the member-to-member composition. -/
noncomputable def between (i j : Fin 2) :
    StableGraphIncidence.Equivalence
      (W3ShiftLimitRows.shiftMembers shrink i).datum
      (W3ShiftLimitRows.shiftMembers shrink j).datum :=
  (memberEquivalence shrink hValid i).symm.trans (memberEquivalence shrink hValid j)

theorem between_row (i j : Fin 2) :
    (between shrink hValid i j).row =
      (rowEquiv shrink hValid i).symm.trans (rowEquiv shrink hValid j) := by
  rw [between]
  change (memberEquivalence shrink hValid i).row.symm.trans
    (memberEquivalence shrink hValid j).row = _
  rw [memberEquivalence_row, memberEquivalence_row]

/-- Position II.b to Position II.a. -/
noncomputable def shrinkToGrow :
    StableGraphIncidence.Equivalence shrink.shrinkCandidate.datum
      shift.growCandidate.datum :=
  (shrinkEquivalence shrink hValid).symm.trans (growEquivalence shrink hValid)

/-- Position II.a to Position II.b. -/
noncomputable def growToShrink :
    StableGraphIncidence.Equivalence shift.growCandidate.datum
      shrink.shrinkCandidate.datum :=
  (growEquivalence shrink hValid).symm.trans (shrinkEquivalence shrink hValid)

/-- Equation (3)'s two members in the pair's common row and target-occurrence
coordinates. -/
noncomputable def commonMatrix (i : Fin 2) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (W3ShiftLimitRows.shiftMembers shrink i).datum
    (rowEquiv shrink hValid i path)
    (occurrenceEquiv target wall (W3ShiftLimitRows.shiftMembers shrink i).right place)

/-- **The retained columns of both members are the incoming ones.** -/
theorem commonMatrix_retained (i : Fin 2) (path : StablePath data)
    (place : target.edges) :
    commonMatrix shrink hValid i path (some place) = matrix data path place := by
  fin_cases i
  · exact shrink_matrix_retained shrink hValid path place
  · exact grow_matrix_retained shrink hValid path place

end Pair

end DraismaVargas.LocalCases.W3ShiftGraphData
