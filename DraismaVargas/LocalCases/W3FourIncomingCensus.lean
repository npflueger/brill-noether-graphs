import DraismaVargas.LocalCases.W3FourRowDescent
import DraismaVargas.LocalCases.W3ShiftIncomingMatching

/-!
# The incoming census at a `w3Four`-classified wall

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a=k4)} (the `w3Four` case:
four members), Figure 28 and Equation (2).

This is the first of the two identification modules of the `w3Four` case (the
second is `W3FourIncomingMatching`).  It answers the
*wall-local* half of "which Figure 28 member is the incoming cover":

* **which direction is isolated** -- `divalentOccurrence_eq_grow_or_other_or_largest`
  and `divalentOccurrence_eq_first_or_second_or_largest`;
* **the member side of the block dictionary**, packaged once as `WallMember`,
  with the three Figure 28 shapes available over one datum as its three
  constructors `growMember`, `positionOneMember`, `positionTwoMember`;
* **that a third member always exists over the incoming cover's own wall
  datum** -- `exists_positionMember`.

## Figure 28's four members, and the three that live over one datum

Part I reads the four members off the two possible values of `α`:

* `α = 4` (`|A₀| = k₄`, which precludes Position II.a).  Position I gives
  `M⁽¹⁾` and Position II.b gives `M⁽²⁾`.  **Both isolate `t₄`.**
* `α = 2` (which precludes Position I, and `|A₀| ≯ max(k_β,k_γ) = k₄`
  precludes Position II.b).  Position II.a gives `M⁽³⁾`, which **isolates
  `t₂`**; the analogous argument at `α = 3` gives `M⁽⁴⁾`, which **isolates
  `t₃`**.

So the isolated direction takes the value `t₄` on `M⁽¹⁾` and `M⁽²⁾` and the two
distinct values `t₂`, `t₃` on `M⁽³⁾`, `M⁽⁴⁾`.  That is the first structural
divergence from Figure 29, where both members of the pair carry the *same* side
predicate and the placement decides nothing: here the divalent original
endpoint's retained direction already separates `{M⁽¹⁾,M⁽²⁾}` from `M⁽³⁾` and
from `M⁽⁴⁾`.

`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint` says that
Position I's hypothesis (`e₂`, `e₃` disjoint) and Position II.b's (a sheet of
`A₀` outside both) are exact negations of one another, so on any **one** datum
value exactly one of `M⁽¹⁾`, `M⁽²⁾` is available -- and one of them always is.
`exists_positionMember` is that observation, packaged: over the incoming
cover's own wall datum there are always **three** Figure 28 members, one for
each of the three surviving directions, and the identification never needs a
gauge copy.

That is the second structural divergence from Figure 29, whose incoming exit
has to allow a branch swap in the hypothesis `shrink`.  Part I works with
isomorphism classes of gluing datums, while a Lean datum is a fixed value; here
the branch swap is needed only to put all **four** members over one datum at
once, which is what Equation (2) needs and what the identification does not.

## What is a hypothesis, and what is not

Nothing in this module.  The direction census is
`W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence`, which is
profile-free, against `W3FourSourceCandidates.GrowProfile.surviving`; the
member dictionaries are `rfl`-level readings of the two assembly shapes
(`W3FourSourceCandidates.GrowProfile.growCandidate` and
`W3FourClosure.FourStarGeometry.reversedCandidate`) through the profile-free
`W3ShiftIncomingCensus.pasted_blocks_selected` / `pasted_blocks_background`.

The **selected block census** -- the literal sheet classes the incoming cover
displays at the two restored endpoints and at the contracted occurrence -- is
not here and not attempted; `W3FourIncomingMatching` takes it as
`W3ShiftIncomingMatching.SelectedCensus`, which is itself profile-free.

## Why `W3ShiftIncomingCensus` is imported

`pasted_blocks_selected`, `pasted_blocks_background` and
`placement_of_movingTarget_eq` mention no `ShiftProfile`, no Figure 29 member
and no shift arithmetic: they are stated for an arbitrary candidate presented
as `LocalResolution.onBlock` and for an arbitrary side predicate agreeing with
the divalent occurrence.  They are consumed verbatim rather than restated.  The
shift chain already sits above `W3FourLimitRows`
(`W3ShiftLimitRows` imports it), so this import adds no new layer.
-/

namespace DraismaVargas.LocalCases.W3FourIncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11 ResolutionCoarseFine
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_spec)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond)
open W3FourClosure (FourStarGeometry ofGrowProfile PositionOne PositionTwo)
open W3FourSurvival (SelectedSurvival)

/-! ## §1  One Figure 28 member, packaged for the identification -/

section Members

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- **One Figure 28 member over one wall datum, with its block dictionary.**

`isolated` is the direction the member places alone at the new divalent
endpoint -- `t₂`, `t₃` or `t₄` -- and `side` says the member's side predicate is
the one that isolates it.  The three `selected*` partitions are the classes the
member displays over the distinguished wall block at the divalent endpoint, at
the trivalent endpoint and on the new edge; the three background fields say
that off that block every member of the case resolves with `isolated`'s own
partition at the divalent endpoint and on the new edge and with the whole wall
partition at the trivalent endpoint.

The background shape is shared by both Figure 28 assemblies, and is the same
one Figure 29's pair carries (`W3ShiftIncomingCensus.grow_*_background`), which
is what lets the matching step be written once. -/
structure WallMember (data : GluingDatum target degree) (wall : target.V)
    (root : Fin degree) where
  /-- The member. -/
  candidate : BalancedGlobal.Candidate target degree data wall
  /-- The direction it places alone at the new divalent endpoint. -/
  isolated : target.edges
  /-- Its side predicate isolates that direction. -/
  side : ∀ edge, candidate.right edge = rightOf isolated edge
  /-- It preserves the complete quotient-source genus.  Every Figure 28 member
  does, because selected and background blocks are pasted stars in one
  orientation or the other. -/
  sourceGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph
  /-- **Its stable incidence graph is the wall datum's**, whenever that datum is
  valid.  This is `W3FourRowDescent`'s row descent at the member, and it is what
  the exit transports an original-coordinate presentation along. -/
  dictionary : data.Valid →
    StableGraphIncidence.Equivalence data candidate.datum
  /-- `A'`: the divalent endpoint's class over the distinguished block. -/
  selectedLeft : SheetPartition degree
  /-- `A⁽ᵠ⁾`: the trivalent endpoint's class. -/
  selectedRight : SheetPartition degree
  /-- `e'`: the new edge's class. -/
  selectedNew : SheetPartition degree
  left_selected : ∀ sheet, (data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).left.block sheet =
      selectedLeft.block sheet
  right_selected : ∀ sheet, (data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).right.block sheet =
      selectedRight.block sheet
  newEdge_selected : ∀ sheet, (data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).newEdge.block sheet =
      selectedNew.block sheet
  left_background : ∀ sheet, ¬(data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).left.block sheet =
      (data.edgePartition isolated).block sheet
  right_background : ∀ sheet, ¬(data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).right.block sheet =
      (data.vertexPartition wall).block sheet
  newEdge_background : ∀ sheet, ¬(data.vertexPartition wall).Rel root sheet →
    (W3Nd2IncomingMemberMatching.pasted candidate).newEdge.block sheet =
      (data.edgePartition isolated).block sheet

end Members

/-! ## §2  The two assembly shapes, read as `onBlock` resolutions -/

section Shapes

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- Figure 28's Position II.a member, as an `onBlock` resolution.  This is the
same reading `W3FourSourceCandidates.GrowProfile.growCandidate_sourceGenus`
performs. -/
theorem growCandidate_resolution (grown : GrowProfile input) (block : Fin degree) :
    grown.growCandidate.resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines) block := rfl

/-- and it isolates its own grow direction. -/
theorem growCandidate_right (grown : GrowProfile input) (edge : target.edges) :
    grown.growCandidate.right edge = rightOf grown.growTarget edge := rfl

/-- Figure 28's Position I and Position II.b members, as `onBlock` resolutions.
Both are `FourStarGeometry.reversedCandidate`, whose selected local resolution
is the **reverse** of the coarse/fine pair: the whole wall block stays at the
divalent endpoint beside `t₄`, and the chosen refinement sits on the new edge
and at the trivalent endpoint. -/
theorem reversedCandidate_resolution (geometry : FourStarGeometry data wall)
    (fine : SheetPartition degree) (hFine : fine.Refines (data.vertexPartition wall))
    (hGrow : (data.edgePartition geometry.growTarget).Refines fine)
    (hOther : (data.edgePartition geometry.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (data.edgePartition geometry.growTarget).blockCountWithin fine sheet +
          (data.edgePartition geometry.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    (block : Fin degree) :
    (geometry.reversedCandidate fine hFine hGrow hOther hCounts).resolution block =
      LocalResolution.onBlock (data.vertexPartition wall) geometry.growAnchor
        ((fineResolution (data.vertexPartition wall) fine hFine).reverse)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition geometry.largestTarget) geometry.largest_refines)
        block := rfl

/-- and they isolate `t₄`. -/
theorem reversedCandidate_right (geometry : FourStarGeometry data wall)
    (fine : SheetPartition degree) (hFine : fine.Refines (data.vertexPartition wall))
    (hGrow : (data.edgePartition geometry.growTarget).Refines fine)
    (hOther : (data.edgePartition geometry.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (data.edgePartition geometry.growTarget).blockCountWithin fine sheet +
          (data.edgePartition geometry.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2)
    (edge : target.edges) :
    (geometry.reversedCandidate fine hFine hGrow hOther hCounts).right edge =
      rightOf geometry.largestTarget edge := rfl

end Shapes

/-! ## §3  The three members over one datum -/

section Constructors

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- **`M⁽³⁾` and `M⁽⁴⁾`, packaged.**  A Position II.a member displays the
enlarged class `e_α ∪ {x}` at the divalent endpoint and on the new edge and the
whole wall block `A₀` at the trivalent endpoint. -/
noncomputable def growMember (grown : GrowProfile input) :
    WallMember data wall input.distinguishedBlock.1 where
  candidate := grown.growCandidate
  isolated := grown.growTarget
  side := growCandidate_right grown
  sourceGenus := grown.growCandidate_sourceGenus
  dictionary := fun hValid ↦ W3FourRowDescent.GrowMember.equivalence grown
    (SelectedSurvival.ofGrowProfile grown) hValid
  selectedLeft := grown.growPartition
  selectedRight := data.vertexPartition wall
  selectedNew := grown.growPartition
  left_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (grown.growAnchor_wall_rel.symm.trans hSel)).1
  right_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (grown.growAnchor_wall_rel.symm.trans hSel)).2.1
  newEdge_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (grown.growAnchor_wall_rel.symm.trans hSel)).2.2
  left_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (fun hRel ↦ hOff (grown.growAnchor_wall_rel.trans hRel))).1
  right_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (fun hRel ↦ hOff (grown.growAnchor_wall_rel.trans hRel))).2.1
  newEdge_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background grown.growCandidate _ _ _
      (growCandidate_resolution grown) sheet
      (fun hRel ↦ hOff (grown.growAnchor_wall_rel.trans hRel))).2.2

@[simp] theorem growMember_candidate (grown : GrowProfile input) :
    (growMember grown).candidate = grown.growCandidate := rfl

@[simp] theorem growMember_isolated (grown : GrowProfile input) :
    (growMember (data := data) (wall := wall) grown).isolated = grown.growTarget := rfl

/-- **`M⁽¹⁾`, packaged.**  Position I keeps the whole wall block `A₀` at the
divalent endpoint beside `t₄` and puts the two-block split of `A₀` into `e₂`
and `e₃` on the new edge and at the trivalent endpoint. -/
noncomputable def positionOneMember (position : PositionOne data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    WallMember data wall root where
  candidate := position.candidate
  isolated := position.largestTarget
  side := reversedCandidate_right position.toFourStarGeometry _ _ _ _ _
  sourceGenus := position.candidate_sourceGenus
  dictionary := fun hValid ↦
    W3FourRowDescent.PositionOne.equivalence position survival hValid
  selectedLeft := data.vertexPartition wall
  selectedRight := position.fine
  selectedNew := position.fine
  left_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).1
  right_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).2.1
  newEdge_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).2.2
  left_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).1
  right_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).2.1
  newEdge_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).2.2

@[simp] theorem positionOneMember_candidate (position : PositionOne data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    (positionOneMember position survival root hRoot).candidate = position.candidate := rfl

@[simp] theorem positionOneMember_isolated (position : PositionOne data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    (positionOneMember position survival root hRoot).isolated =
      position.largestTarget := rfl

/-- **`M⁽²⁾`, packaged.**  Position II.b keeps `A₀` at the divalent endpoint
beside `t₄` and puts `A₀` minus the residual sheet on the new edge and at the
trivalent endpoint. -/
noncomputable def positionTwoMember (position : PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    WallMember data wall root where
  candidate := position.candidate
  isolated := position.largestTarget
  side := reversedCandidate_right position.toFourStarGeometry _ _ _ _ _
  sourceGenus := position.candidate_sourceGenus
  dictionary := fun hValid ↦
    W3FourRowDescent.PositionTwo.equivalence position survival hValid
  selectedLeft := data.vertexPartition wall
  selectedRight := position.fine
  selectedNew := position.fine
  left_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).1
  right_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).2.1
  newEdge_selected := fun sheet hSel ↦
    (W3ShiftIncomingCensus.pasted_blocks_selected position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (hRoot.symm.trans hSel)).2.2
  left_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).1
  right_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).2.1
  newEdge_background := fun sheet hOff ↦
    (W3ShiftIncomingCensus.pasted_blocks_background position.candidate _ _ _
      (reversedCandidate_resolution position.toFourStarGeometry _ _ _ _ _) sheet
      (fun hRel ↦ hOff (hRoot.trans hRel))).2.2

@[simp] theorem positionTwoMember_candidate (position : PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    (positionTwoMember position survival root hRoot).candidate = position.candidate := rfl

@[simp] theorem positionTwoMember_isolated (position : PositionTwo data wall)
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root position.growAnchor) :
    (positionTwoMember position survival root hRoot).isolated =
      position.largestTarget := rfl

/-- **A Figure 28 member isolating `t₄` exists over *every* datum of the case.**

Position I needs `e₂` and `e₃` disjoint and Position II.b needs a sheet of `A₀`
outside both, and by `W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`
(restated for the packaged geometry as `W3FourClosure.exists_outside_sheet`)
those are exact negations, both readable off `k₂ + k₃ = |A₀|`.  So the case
dichotomy is not a hypothesis: whichever way it falls, one of `M⁽¹⁾`, `M⁽²⁾` is
available, and the incoming identification never has to leave the incoming
cover's own wall datum.

This cannot be said for Figure 29, whose Position II.b member genuinely may
fail to exist over the incoming datum
(`W3ShiftSourceCandidates.shift_arithmetic_does_not_force_shrinkSheet`); there
the branch swap is unavoidable, here it is not. -/
theorem exists_positionMember (geometry : FourStarGeometry data wall)
    (survival : SelectedSurvival data wall geometry)
    (root : Fin degree)
    (hRoot : (data.vertexPartition wall).Rel root geometry.growAnchor) :
    ∃ member : WallMember data wall root, member.isolated = geometry.largestTarget := by
  classical
  by_cases hDisjoint : Disjoint ((data.edgePartition geometry.growTarget).block
      geometry.growAnchor)
    ((data.edgePartition geometry.otherTarget).block geometry.otherAnchor)
  · exact ⟨positionOneMember
      { toFourStarGeometry := geometry, disjoint := hDisjoint } survival root hRoot, rfl⟩
  · obtain ⟨sheet, hWall, hGrow, hOther⟩ :=
      W3FourClosure.exists_outside_sheet geometry hDisjoint
    exact ⟨positionTwoMember
      { toFourStarGeometry := geometry, outside := sheet, outside_wall := hWall,
        outside_grow := hGrow, outside_other := hOther } survival root hRoot, rfl⟩

end Constructors

/-! ## §4  Which of Figure 28's three directions the incoming cover isolates -/

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

/-- **Figure 28's three orientations, as a trichotomy on the incoming cover.**

The unique retained wall direction at the divalent original endpoint is the
direction of one of the distinguished block's three survivors, because
`W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence` produces a
survivor above it and `W3FourSourceCandidates.GrowProfile.surviving` lists the
survivors as exactly `{grow, other, largest}`.

The census input is profile-free -- it mentions no `Nd2Profile`, no
`Nd3Profile` and no figure -- so the `w3Four` case pays nothing for it, exactly
as the shift case does not. -/
theorem divalentOccurrence_eq_grow_or_other_or_largest (grown : GrowProfile input) :
    divalentOccurrence data hc hab hOne fullDim star = grown.growTarget ∨
      divalentOccurrence data hc hab hOne fullDim star = grown.otherTarget ∨
        divalentOccurrence data hc hab hOne fullDim star = grown.largestTarget := by
  classical
  obtain ⟨mapped, hSurvives, hTarget⟩ :=
    W3Nd3IncomingCensus.exists_survivor_over_divalentOccurrence data hc hab hOne
      fullDim hForest hCompat star input
  have hMember : mapped ∈ survivors (contractDatum data hc hab hOne)
      input.distinguishedBlock :=
    (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock
      mapped).mpr hSurvives
  rw [grown.surviving] at hMember
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMember
  rcases hMember with hGrow | hOther | hLargest
  · exact Or.inl (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hGrow))
  · exact Or.inr (Or.inl (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hOther)))
  · exact Or.inr (Or.inr (hTarget.symm.trans (congrArg
      (fun edge : IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock) ↦ edge.1.1.1) hLargest)))

/-- **The same trichotomy stated on the `w3Four` classification payload.**  The
hypotheses are exactly the fields of
`W3IncomingClassification.Classification.four`: an `Nd3Profile` of the
distinguished block, three distinct target directions, and the largest index
equal to `|A₀|`.

The three values are `t₂`, `t₃`, `t₄` -- the directions of `M⁽³⁾`, `M⁽⁴⁾` and
of the pair `M⁽¹⁾`, `M⁽²⁾`. -/
theorem divalentOccurrence_eq_first_or_second_or_largest
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) :
    divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1 ∨
      divalentOccurrence data hc hab hOne fullDim star = profile.second.1.1.1 ∨
        divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1 :=
  divalentOccurrence_eq_grow_or_other_or_largest data hc hab hOne fullDim hForest
    hCompat star input (growProfileFirst profile directions largest_index)

end Divalent

/-! ## §5  The placement and the target isomorphism -/

section Placement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)

/-- **The target placement of a Figure 28 member whose isolated direction is
the incoming cover's own.**  Unlike Figure 29, the three members carry three
*different* side predicates, so this is already a per-member statement; what
makes it uniform is that each member's predicate is `rightOf` of its own
isolated direction.

`W3ShiftIncomingCensus.placement_of_movingTarget_eq` is consumed verbatim: it
mentions no `ShiftProfile` and no Figure 29 member, only an arbitrary side
predicate agreeing with `rightOf` of the divalent occurrence. -/
theorem member_placement {root : Fin degree}
    (member : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩ root)
    (hIsolated : member.isolated = divalentOccurrence data hc hab hOne fullDim star) :
    IncomingMatchingCore.Placement hc hab hOne member.candidate.right :=
  W3ShiftIncomingCensus.placement_of_movingTarget_eq data hc hab hOne fullDim star _
    (fun edge ↦ (member.side edge).trans
      (congrArg (fun place ↦ rightOf place edge) hIsolated))

/-- **The literal target isomorphism to a Figure 28 member.**  This is
`IncomingMatchingCore.memberTargetIso`; no wrapper per member is needed. -/
noncomputable def memberTargetIso {root : Fin degree}
    (member : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩ root)
    (hIsolated : member.isolated = divalentOccurrence data hc hab hOne fullDim star) :
    Utilities.CFGraphIso target
      (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩
        member.candidate.right) :=
  IncomingMatchingCore.memberTargetIso data hc hab hOne member.candidate
    (member_placement data hc hab hOne fullDim star member hIsolated)

/-- Every literal incoming `Option` occurrence, the restored contracted
occurrence `none` included, is carried to the corresponding member column. -/
theorem memberTargetIso_occurrence {root : Fin degree}
    (member : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩ root)
    (hIsolated : member.isolated = divalentOccurrence data hc hab hOne fullDim star)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne fullDim star member
        hIsolated)
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        member.candidate.right column :=
  IncomingMatchingCore.memberTargetIso_occurrence data hc hab hOne member.candidate
    (member_placement data hc hab hOne fullDim star member hIsolated) hConnected hGenus
    column

end Placement

end DraismaVargas.LocalCases.W3FourIncomingCensus
