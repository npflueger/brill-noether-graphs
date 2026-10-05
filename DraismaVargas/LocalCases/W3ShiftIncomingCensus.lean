module

public import DraismaVargas.LocalCases.W3ShiftLimitRows
public import DraismaVargas.LocalCases.W3Nd3IncomingCensus
public import DraismaVargas.LocalCases.IncomingMatchingCore
public import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching

@[expose] public section

/-!
# The incoming census at a `w3Shift`-classified wall

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

This is the first of the two modules the incoming-member identification of the
`w3Shift` case needs.  It answers the *wall-local* half of "which Figure 29 member is
the incoming cover":

* **which direction moved** -- `divalentOccurrence_eq_moving_or_first_or_second`
  and `exists_shiftProfile_movingTarget_eq_divalent`;
* **the target placement** -- `placement_of_movingTarget_eq`, `shiftTargetIso`
  and `shiftTargetIso_occurrence`, valid for *both* members at once;
* **the member side of the block dictionary** -- `pasted_blocks_selected` and
  `pasted_blocks_background` with their six named instances for Figure 29's
  shrink and grow members.

The second module, `W3ShiftIncomingMatching`, turns these into the three wall
comparisons, the pointwise `SameBlocks` families and the normalization receipt.

## Why the direction census is cheap here, and the nd3 census is not

`W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence` is **profile-free**:
it takes only an incoming full-dimensional presentation, the contraction forest,
dangling compatibility, a trivalent contracted wall and a `W3SourceInput`, and
produces a *surviving* occurrence of the distinguished wall block above the
divalent original endpoint's retained direction.  A `ShiftProfile` lists the
distinguished block's survivors as `{moving, firstRest, secondRest}`
(`ShiftProfile.surviving`), so that one census immediately gives the three-way
dichotomy, and Figure 29's three orientations
(`W3ShiftSourceCandidates.shiftProfileLargest` / `First` / `Second`) turn the
dichotomy into a **choice of orientation**: there is always a `ShiftProfile`
whose moving direction is the incoming cover's own isolated direction.  That is
exactly what Equation (3)'s independence of the three pairs needs, and it is why
`W3ShiftClosure.exists_equationThree_positive_exit` is
stated for an arbitrary orientation.

What is *not* cheap, and is not attempted in this module, is the **selected
block census**: the literal sheet classes the incoming cover displays at the
two restored endpoints and at the contracted occurrence.  In nd3 that is
`W3Nd3IncomingCensus.selected_fibre_census_of_shared` / `_of_largest` and
`selected_sheet_classes_of_shared` / `_of_largest`, on top of the pruned-fibre
theory.  `W3ShiftIncomingMatching` takes those three facts as a named hypothesis
bundle and says so; `W3ShiftClosureUnconditional.exists_shiftProfile_selectedCensus`
supplies them.

## Both Figure 29 members carry the *same* side predicate

`ShiftProfile.background` sets `right := W3Nd2SourceCandidates.rightOf
shift.movingTarget`, and both the Position II.a grow member and the Position
II.b shrink member are assembled on that one background, so

`growCandidate_right` and `shrinkCandidate_right` are both `rfl`.

Consequently the **placement is not what separates the pair**: `Placement` holds
for both members as soon as the incoming isolated direction is the moving one.
What separates them is the block dictionary at the distinguished block -- the
grow member enlarges the moving class by one sheet and keeps the whole wall
block at the trivalent end, while the shrink member keeps the moving class and
detaches one sheet from both the new edge and the trivalent end -- and, as a
numerical shadow of that, `W3ShiftLimitRows.shiftMembers_ne`'s `k_α ∓ 1`.

## The gauge copy, and where it does **not** enter

`W3ShiftClosure.exists_gauge_shift_pair` produces Equation (3)'s pair over a
*branch-swapped copy* `gaugeData` of the wall datum, because Position II.b's
sheet need not exist on the wall datum itself (Part I works with gluing data up
to isomorphism, where the branch swap identifies the two).  **Nothing in this module or in
`W3ShiftIncomingMatching` uses that copy.**  Both modules work over the
incoming cover's own wall datum `contractDatum data hc hab hOne`: the incoming
cover *is* a member over that datum or it is not a Figure 29 member at all, and
an identification against a member over `gaugeData` would compare the incoming
cover's partitions with partitions that differ from them by the branch swap.

The consequence, stated once and carried through `W3ShiftIncomingMatching` and
the exit (`W3ShiftGraphTracking`, `W3ShiftTrackedFinal`): the identification lands
over `contractDatum data`, and Equation (3)'s *partner* member must therefore be
produced over `contractDatum data` too.  For an incoming cover in Position II.b
that is automatic -- the cover itself exhibits Position II.b's sheet, so
`W3ShiftSourceCandidates.ShrinkData` exists over the wall datum and both members
live there.  For an incoming cover in Position II.a it is exactly
`W3ShiftSourceCandidates.HasShrinkSheet` on the incoming wall datum, which the
case does not supply; the branch swap is then unavoidable, and it is performed on
the incoming datum (`W3ShiftIncomingTransport`, `W3ShiftTrackedFinal`).

## What is deliberately not here

No determinant, no length matrix, no stable row: this module is entirely about
sheet blocks and target directions.  Nothing here goes near
`W3ShiftClosure.LimitRows`, and nothing here assumes a `ShrinkData` exists.
-/

namespace DraismaVargas.LocalCases.W3ShiftIncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11 ResolutionCoarseFine
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_spec
  divalentOccurrence_placement)
open W3ShiftSourceCandidates

/-! ## The member side of the block dictionary

Both Figure 29 members are `ResolutionM11.LocalResolution.onBlock` of a
*selected* local resolution against the one background resolution
`ShiftProfile.background` installs.  The three pasted wall partitions of such a
candidate are therefore read off blockwise, and the six dictionary facts the
matching step consumes are the two instances below at each of the three
positions. -/

section Pasted

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- The background local resolution both Figure 29 members are assembled on:
`ResolutionCoarseFine.fineResolution` of the moving direction's own edge
partition.  Its left endpoint and new edge are `e_α`, its right endpoint the
whole wall partition. -/
noncomputable def backgroundResolution (shift : ShiftProfile input) :
    LocalResolution degree :=
  fineResolution (data.vertexPartition wall) (data.edgePartition shift.movingTarget)
    shift.movingTarget_refines

/-- **The three pasted wall partitions on the distinguished block.**  Stated for
an arbitrary candidate presented as `onBlock`, so that the grow and the shrink
member are two instances of one lemma. -/
theorem pasted_blocks_selected
    (C : BalancedGlobal.Candidate target degree data wall)
    (anchor : Fin degree) (selected background : LocalResolution degree)
    (hRes : ∀ block, C.resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) anchor selected
        (fun _ ↦ background) block)
    (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel anchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted C).left.block sheet =
        selected.left.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet =
        selected.right.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet =
        selected.newEdge.block sheet := by
  have hRepr : (data.vertexPartition wall).Rel anchor
      ((data.vertexPartition wall).repr sheet) :=
    hSel.trans ((data.vertexPartition wall).rel_repr_left sheet).symm
  have hLocal : C.resolution ((data.vertexPartition wall).repr sheet) = selected := by
    rw [hRes, LocalResolution.onBlock_of_rel _ _ _ _ _ hRepr]
  refine ⟨?_, ?_, ?_⟩
  · rw [LocalResolution.pasteLeft_block, hLocal]
  · rw [LocalResolution.pasteRight_block, hLocal]
  · rw [LocalResolution.pasteNewEdge_block, hLocal]

/-- The same off the distinguished block. -/
theorem pasted_blocks_background
    (C : BalancedGlobal.Candidate target degree data wall)
    (anchor : Fin degree) (selected background : LocalResolution degree)
    (hRes : ∀ block, C.resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) anchor selected
        (fun _ ↦ background) block)
    (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel anchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted C).left.block sheet =
        background.left.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet =
        background.right.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet =
        background.newEdge.block sheet := by
  have hRepr : ¬(data.vertexPartition wall).Rel anchor
      ((data.vertexPartition wall).repr sheet) := fun hRel ↦
    hOff (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hLocal : C.resolution ((data.vertexPartition wall).repr sheet) = background := by
    rw [hRes, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRepr]
  refine ⟨?_, ?_, ?_⟩
  · rw [LocalResolution.pasteLeft_block, hLocal]
  · rw [LocalResolution.pasteRight_block, hLocal]
  · rw [LocalResolution.pasteNewEdge_block, hLocal]

/-- Figure 29's Position II.a member, as an `onBlock` resolution. -/
theorem growCandidate_resolution (shift : ShiftProfile input) (block : Fin degree) :
    shift.growCandidate.resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        (fineResolution (data.vertexPartition wall) shift.growPartition
          shift.growPartition_refines)
        (fun _ ↦ backgroundResolution shift) block := rfl

/-- Figure 29's Position II.b member, as an `onBlock` resolution. -/
theorem shrinkCandidate_resolution {shift : ShiftProfile input}
    (shrink : ShrinkData shift) (block : Fin degree) :
    shrink.shrinkCandidate.resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        shrink.selected (fun _ ↦ backgroundResolution shift) block := rfl

/-! ### The six dictionary facts of the grow member -/

/-- `A' = e_α ∪ {x}` at the new divalent endpoint. -/
theorem grow_left_selected (shift : ShiftProfile input) (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).left.block sheet =
      shift.growPartition.block sheet :=
  (pasted_blocks_selected shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hSel).1

/-- The whole wall block `A₀` stays at the trivalent endpoint. -/
theorem grow_right_selected (shift : ShiftProfile input) (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).right.block sheet =
      (data.vertexPartition wall).block sheet :=
  (pasted_blocks_selected shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hSel).2.1

/-- `|e'| = k_α + 1` on the new edge: the same enlarged class. -/
theorem grow_newEdge_selected (shift : ShiftProfile input) (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).newEdge.block sheet =
      shift.growPartition.block sheet :=
  (pasted_blocks_selected shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hSel).2.2

theorem grow_left_background (shift : ShiftProfile input) (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).left.block sheet =
      (data.edgePartition shift.movingTarget).block sheet :=
  (pasted_blocks_background shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hOff).1

theorem grow_right_background (shift : ShiftProfile input) (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).right.block sheet =
      (data.vertexPartition wall).block sheet :=
  (pasted_blocks_background shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hOff).2.1

theorem grow_newEdge_background (shift : ShiftProfile input) (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shift.growCandidate).newEdge.block sheet =
      (data.edgePartition shift.movingTarget).block sheet :=
  (pasted_blocks_background shift.growCandidate _ _ _
    (growCandidate_resolution shift) sheet hOff).2.2

/-! ### The six dictionary facts of the shrink member -/

/-- `A' = e_α`, unchanged, at the new divalent endpoint. -/
theorem shrink_left_selected {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).left.block sheet =
      (data.edgePartition shift.movingTarget).block sheet :=
  (pasted_blocks_selected shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hSel).1

/-- `A⁽ᵠ⁾ = A₀ ∖ {x}` at the trivalent endpoint. -/
theorem shrink_right_selected {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).right.block sheet =
      ((data.vertexPartition wall).detachSheet shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_wall_rel).block sheet :=
  (pasted_blocks_selected shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hSel).2.1

/-- `|e'| = k_α − 1` on the new edge: the moving class minus the transferred
sheet. -/
theorem shrink_newEdge_selected {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).newEdge.block sheet =
      ((data.edgePartition shift.movingTarget).detachSheet shrink.transfer
        shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving).block
        sheet :=
  (pasted_blocks_selected shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hSel).2.2

theorem shrink_left_background {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).left.block sheet =
      (data.edgePartition shift.movingTarget).block sheet :=
  (pasted_blocks_background shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hOff).1

theorem shrink_right_background {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).right.block sheet =
      (data.vertexPartition wall).block sheet :=
  (pasted_blocks_background shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hOff).2.1

theorem shrink_newEdge_background {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted shrink.shrinkCandidate).newEdge.block sheet =
      (data.edgePartition shift.movingTarget).block sheet :=
  (pasted_blocks_background shrink.shrinkCandidate _ _ _
    (shrinkCandidate_resolution shrink) sheet hOff).2.2

/-! ### Both members carry the moving direction's side predicate -/

/-- The Position II.a member isolates the moving direction. -/
theorem growCandidate_right (shift : ShiftProfile input) (edge : target.edges) :
    shift.growCandidate.right edge = rightOf shift.movingTarget edge := rfl

/-- The Position II.b member isolates the same direction. -/
theorem shrinkCandidate_right {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (edge : target.edges) :
    shrink.shrinkCandidate.right edge = rightOf shift.movingTarget edge := rfl

end Pasted

/-! ## Which of Figure 29's three directions the incoming cover moved -/

section Divalent

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include hForest hCompat

/-- **Figure 29's three orientations, as a dichotomy on the incoming cover.**
The unique retained wall direction at the divalent original endpoint is the
direction of one of the distinguished block's three survivors, because
`W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence` produces a
survivor above it and `ShiftProfile.surviving` lists the survivors as exactly
those three.

The census input is profile-free -- it mentions no `Nd2Profile`, no
`Nd3Profile` and no figure -- so the shift case pays nothing for it. -/
theorem divalentOccurrence_eq_moving_or_first_or_second (shift : ShiftProfile input) :
    divalentOccurrence data hc hab hOne fullDim star = shift.movingTarget ∨
      divalentOccurrence data hc hab hOne fullDim star = shift.firstTarget ∨
        divalentOccurrence data hc hab hOne fullDim star = shift.secondTarget := by
  classical
  obtain ⟨mapped, hSurvives, hTarget⟩ :=
    W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence data hc hab hOne
      fullDim hForest hCompat star input
  have hMember : mapped ∈ survivors (contractDatum data hc hab hOne)
      input.distinguishedBlock :=
    (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock
      mapped).mpr hSurvives
  rw [shift.surviving] at hMember
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMember
  rcases hMember with hMoving | hFirst | hSecond
  · exact Or.inl (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hMoving))
  · exact Or.inr (Or.inl (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hFirst)))
  · exact Or.inr (Or.inr (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hSecond)))

/-- **The incoming cover's own Figure 29 orientation.**  From the `w3Shift`
classification payload -- an `Nd3Profile` of the distinguished block with three
distinct target directions and the largest index strictly below `|A₀|`, which is
exactly `W3IncomingClassification.Classification.shift`'s data -- there is a
`ShiftProfile` whose moving direction is the incoming cover's isolated one, and
it satisfies the case hypothesis `k_β, k_γ < |A₀|` that Position II.b's clearing
step consumes.

This is what makes the *two*-member family of `W3ShiftClosure` the right one:
Equation (3)'s three pairs balance independently, so only the
pair on the incoming cover's own direction is needed, and this theorem produces
precisely that direction. -/
theorem exists_shiftProfile_movingTarget_eq_divalent
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 <
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) :
    ∃ shift : ShiftProfile input,
      shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star ∧
        W3ShiftClosure.RetainedBelow shift := by
  obtain ⟨hLargest, hFirst, hSecond⟩ :=
    W3ShiftClosure.retainedBelow_of_largest_lt profile directions largest_lt
  rcases divalentOccurrence_eq_moving_or_first_or_second data hc hab hOne fullDim
      hForest hCompat star input (shiftProfileLargest profile directions largest_lt) with
    hMoving | hRest
  · exact ⟨shiftProfileLargest profile directions largest_lt, hMoving.symm, hLargest⟩
  · rcases hRest with hFirstDir | hSecondDir
    · exact ⟨shiftProfileFirst profile directions largest_lt, hFirstDir.symm, hFirst⟩
    · exact ⟨shiftProfileSecond profile directions largest_lt, hSecondDir.symm, hSecond⟩

omit hForest hCompat

/-- **The target placement of *both* Figure 29 members.**  `ShiftProfile.background`
gives the grow and the shrink member the one side predicate
`W3Nd2SourceCandidates.rightOf shift.movingTarget`, so once the incoming cover's
isolated direction is the moving one, the actual incoming target placement is
that of either member.

The placement is therefore **not** the observable that separates the pair, and
that is the first structural divergence from nd2 and nd3, where the two members
carry opposite side predicates and the placement decides between them. -/
theorem placement_of_movingTarget_eq
    (side : (contract target hab hOne).edges → Bool)
    (hSide : ∀ edge, side edge = rightOf (divalentOccurrence data hc hab hOne
      fullDim star) edge) :
    IncomingMatchingCore.Placement hc hab hOne side := by
  have hPlacement := divalentOccurrence_placement data hc hab hOne fullDim star
  rcases hPlacement with hDirect | hFlipped
  · exact Or.inl (fun edge hEdge ↦ (hDirect edge hEdge).trans (hSide edge).symm)
  · exact Or.inr (fun edge hEdge ↦ (hFlipped edge hEdge).trans
      (congrArg (fun value ↦ !value) (hSide edge).symm))

/-- The grow member's placement. -/
theorem grow_placement (shift : ShiftProfile input)
    (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star) :
    IncomingMatchingCore.Placement hc hab hOne shift.growCandidate.right :=
  placement_of_movingTarget_eq data hc hab hOne fullDim star _
    (fun edge ↦ (growCandidate_right shift edge).trans
      (congrArg (fun place ↦ rightOf place edge) hMoving))

/-- The shrink member's placement. -/
theorem shrink_placement {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star) :
    IncomingMatchingCore.Placement hc hab hOne shrink.shrinkCandidate.right :=
  placement_of_movingTarget_eq data hc hab hOne fullDim star _
    (fun edge ↦ (shrinkCandidate_right shrink edge).trans
      (congrArg (fun place ↦ rightOf place edge) hMoving))

/-- **The literal target isomorphism to a Figure 29 member.**  This is
`IncomingMatchingCore.memberTargetIso` at the shift case's members; no wrapper
per member is needed, because the placement above is shared. -/
noncomputable def shiftTargetIso
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hPlacement : IncomingMatchingCore.Placement hc hab hOne C.right) :
    Utilities.CFGraphIso target
      (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ C.right) :=
  IncomingMatchingCore.memberTargetIso data hc hab hOne C hPlacement

/-- Every literal incoming `Option` occurrence, the restored contracted
occurrence `none` included, is carried to the corresponding member column. -/
theorem shiftTargetIso_occurrence
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hPlacement : IncomingMatchingCore.Placement hc hab hOne C.right)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (shiftTargetIso data hc hab hOne C hPlacement)
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ C.right
        column :=
  IncomingMatchingCore.memberTargetIso_occurrence data hc hab hOne C hPlacement
    hConnected hGenus column

end Divalent

end DraismaVargas.LocalCases.W3ShiftIncomingCensus
