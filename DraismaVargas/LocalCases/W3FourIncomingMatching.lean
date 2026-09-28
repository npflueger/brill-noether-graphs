import DraismaVargas.LocalCases.W3FourIncomingCensus

/-!
# Matching an incoming `w3Four` datum to a named Figure 28 member

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a=k4)}, Figure 28 and
Equation (2).

This is the second of the two identification modules of the `w3Four` case.
Given

* the incoming cover's own isolated direction
  (`W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest`),
* the member-side block dictionary (`W3FourIncomingCensus.WallMember`), and
* the **selected block census** -- the three literal sheet classes the incoming
  cover displays at the two restored endpoints and at the contracted
  occurrence, taken here as the profile-free hypothesis bundle
  `W3ShiftIncomingMatching.SelectedCensus` --

it produces the three wall comparisons, the pointwise `SameBlocks` families
against a named Figure 28 member, and the normalization receipt, through the
`n = 3` member-exit combinator
`IncomingMatchingCore.exists_member_normalization_of_family`.

## The selector is the isolated direction, not a class triple

Figure 29's two members carry the *same* side predicate, so
`W3ShiftIncomingMatching` has to separate them by the class triple they display
and prove that triple injective (`shiftClasses_ne`).  Figure 28 is different:
Part I reads `M⁽¹⁾`, `M⁽²⁾` off `α = 4` and `M⁽³⁾`, `M⁽⁴⁾` off `α = 2`,
`α = 3`, so the three available members isolate the three **distinct**
directions `t₄`, `t₂`, `t₃`, and the divalent original endpoint's retained
direction already names the member.  `figure28Directions_injective` is that
separation, and it is a consequence of the profile's own
`first_target_ne` / `second_target_ne` and of the classification payload's
`directions`, with no new arithmetic.

Consequently the selected census is consumed **conditionally**: only the
member the direction names has to display the incoming cover's classes.

## Three members, unconditionally, over the incoming cover's own wall datum

`W3FourIncomingCensus.exists_positionMember` supplies the `t₄` member of the
family over any datum of the case, because Position I's disjointness hypothesis
and Position II.b's residual sheet are exact negations.  So, unlike
`W3ShiftIncomingMatching`, this module needs **no gauge copy and no branch
swap**: every member of the identification family lives over
`contractDatum data hc hab hOne`.  The branch swap (needed because Part I works
with isomorphism classes of gluing datums, while a Lean datum is a fixed value)
is what puts all *four* members over one datum at once, which is Equation (2)'s
business
(`W3FourClosure.exists_equationTwo_family`), not the identification's.

## What is a hypothesis here, and what would discharge it

`W3ShiftIncomingMatching.SelectedCensus` -- the exact analogue of
`W3Nd3IncomingCensus.selected_sheet_classes_of_shared` / `_of_largest` and of
`W3Nd2IncomingSelectedCensus.selected_fibre_census`.  Discharging it needs the
incoming census at a trivalent wall, and it is **not** attempted here
(`W3FourSelectedCensus` produces it); it is the same bundle Figure 29
hypothesises, reused rather than restated.  Nothing else in this module is
hypothesised: the direction census, the placement, the member dictionary, the
`r = 0` background census, the whole-cover exhaustion and the normalization
receipt are all proved here or taken from other modules.

`W3ShiftIncomingMatching.wall_blocks_of_free_dictionary` -- the core's item H
with all three selected positions free -- is consumed verbatim.  Figure 28
needs the free shape for the same reason Figure 29 does and then some: `M⁽³⁾`
and `M⁽⁴⁾` put `e_α ∪ {x}` at the new divalent endpoint, and `M⁽¹⁾`, `M⁽²⁾` put
the refinement of `A₀` at the *trivalent* endpoint and on the new edge, so
neither `hLeftSelected`'s nor `hVSelected`'s fixed target
`mergedPartition data a b` is right for all three.
-/

namespace DraismaVargas.LocalCases.W3FourIncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11 ResolutionCoarseFine
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_spec
  endpoint_valencies)
open W3ShiftIncomingMatching (SelectedCensus merged_eq_wall merged_block_eq_wall_block
  merged_rel_iff_wall_rel wall_blocks_of_free_dictionary)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond)
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourIncomingCensus

/-! ## §1  The pointwise match against one Figure 28 member -/

section Matching

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include hForest

/-- **An incoming `w3Four` cover matches a Figure 28 member, pointwise.**

Stated for an arbitrary `W3FourIncomingCensus.WallMember` over the incoming
cover's own wall datum whose isolated direction is the incoming cover's; the
three members `M⁽¹⁾`/`M⁽²⁾`, `M⁽³⁾` and `M⁽⁴⁾` are its instances.  The three
wall comparisons come from `W3ShiftIncomingMatching.wall_blocks_of_free_dictionary`,
the vertex/occurrence exhaustion from
`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`, and the `r = 0`
background from the profile-free `W3Nd2IncomingMemberMatching.background_*`
family. -/
theorem member_sameBlocks
    (member : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
      input.distinguishedBlock.1)
    (hIsolated : member.isolated = divalentOccurrence data hc hab hOne fullDim star)
    (hCensus : SelectedCensus data hc hab hOne star input member.selectedLeft
      member.selectedRight member.selectedNew) :
    (∀ vertex, ((GluingTransport.transport
          (W3FourIncomingCensus.memberTargetIso data hc hab hOne fullDim star member
            hIsolated)
          data).vertexPartition vertex).SameBlocks
        (member.candidate.datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (W3FourIncomingCensus.memberTargetIso data hc hab hOne fullDim star member
            hIsolated)
          data).edgePartition edge).SameBlocks
        (member.candidate.datum.edgePartition edge)) := by
  classical
  have hSideDiv : ∀ edge, member.candidate.right edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (member.side edge).trans (congrArg (fun place ↦ rightOf place edge) hIsolated)
  have hFlagEq : ∀ sheet, (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block sheet =
      ((contractDatum data hc hab hOne).edgePartition member.isolated).block sheet := by
    intro sheet
    rw [hIsolated, contractDatum_edgePartition]
  have hMerged : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet ↔
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel input.distinguishedBlock.1 sheet :=
    merged_rel_iff_wall_rel data hc hab hOne input.distinguishedBlock.1
  have hLeftSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).left.block sheet =
        member.selectedLeft.block sheet :=
    fun sheet h ↦ member.left_selected sheet ((hMerged sheet).mp h)
  have hRightSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).right.block sheet =
        member.selectedRight.block sheet :=
    fun sheet h ↦ member.right_selected sheet ((hMerged sheet).mp h)
  have hNewSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).newEdge.block sheet =
        member.selectedNew.block sheet :=
    fun sheet h ↦ member.newEdge_selected sheet ((hMerged sheet).mp h)
  have hLeftBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).left.block sheet =
        ((contractDatum data hc hab hOne).edgePartition member.isolated).block sheet :=
    fun sheet h ↦ member.left_background sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
  have hRightBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).right.block sheet =
        (mergedPartition data a b).block sheet := by
    intro sheet h
    rw [merged_block_eq_wall_block data hc hab hOne sheet]
    exact member.right_background sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
  have hNewBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted member.candidate).newEdge.block sheet =
        ((contractDatum data hc hab hOne).edgePartition member.isolated).block sheet :=
    fun sheet h ↦ member.newEdge_background sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
  have hPlacement := W3FourIncomingCensus.member_placement data hc hab hOne fullDim star
    member hIsolated
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hLeftDiv, _, _, _⟩ | ⟨_, hRightDiv, _, _⟩
  · obtain ⟨hU, hV, hNew⟩ := hCensus.divalentLeft hLeftDiv
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈
          GluingDatum.incidentEdges a :=
      (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
        (divalentOccurrence_spec data hc hab hOne fullDim star).1).mp
        (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab hOne
          fullDim star hLeftDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ :=
      wall_blocks_of_free_dictionary data hc hab hOne member.candidate input.distinguishedBlock.1 a b _
        _ member.selectedLeft member.selectedRight member.selectedNew hFlagEq hFlagAt
        (contracted_mem_incidentEdges_left hc)
        (fun edge hEdge sheet hOff ↦
          W3Nd2IncomingMemberMatching.background_edge_block_eq_of_left_divalent data hc hab
            hOne fullDim hForest input hLeftDiv edge hEdge sheet hOff)
        (fun sheet hOff ↦
          W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_left_divalent data hc
            hab hOne fullDim hForest input hLeftDiv sheet hOff)
        hU hV hNew hLeftSel' hRightSel' hNewSel' hLeftBg' hRightBg' hNewBg'
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_left_divalent data hc hab hOne
        fullDim star member.candidate.right hPlacement hSideDiv hLeftDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus member.candidate hPlacement
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew
  · obtain ⟨hU, hV, hNew⟩ := hCensus.divalentRight hRightDiv
    have hFlagAt : unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star) ∈
          GluingDatum.incidentEdges b :=
      (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
        (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab hOne
          fullDim star hRightDiv)
    obtain ⟨hBlockLeft, hBlockRight, hBlockNew⟩ :=
      wall_blocks_of_free_dictionary data hc hab hOne member.candidate input.distinguishedBlock.1 b a _
        _ member.selectedLeft member.selectedRight member.selectedNew hFlagEq hFlagAt
        (contracted_mem_incidentEdges_right hc)
        (fun edge hEdge sheet hOff ↦
          W3Nd2IncomingMemberMatching.background_edge_block_eq_of_right_divalent data hc hab
            hOne fullDim hForest input hRightDiv edge hEdge sheet hOff)
        (fun sheet hOff ↦
          W3Nd2IncomingMemberMatching.background_trivalent_block_eq_of_right_divalent data hc
            hab hOne fullDim hForest input hRightDiv sheet hOff)
        hU hV hNew hLeftSel' hRightSel' hNewSel' hLeftBg' hRightBg' hNewBg'
    obtain ⟨hTransLeft, hTransRight⟩ :=
      W3Nd2IncomingMemberMatching.transported_endpoints_of_right_divalent data hc hab hOne
        fullDim star member.candidate.right hPlacement hSideDiv hRightDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus member.candidate hPlacement
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew

end Matching

/-! ## §2  Figure 28's three members over one datum, as one family -/

section Family

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- **Figure 28's identification family.**  Index `0` is the `t₄` member --
`M⁽¹⁾` if `e₂` and `e₃` are disjoint and `M⁽²⁾` otherwise, supplied by
`W3FourIncomingCensus.exists_positionMember` -- and indices `1`, `2` are the
Position II.a members `M⁽³⁾`, `M⁽⁴⁾` on the two smaller directions. -/
noncomputable def figure28Members
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (positionMember : WallMember data wall input.distinguishedBlock.1) :
    Fin 3 → WallMember data wall input.distinguishedBlock.1 :=
  ![positionMember,
    growMember (growProfileFirst profile directions largest_index),
    growMember (growProfileSecond profile directions largest_index)]

/-- Figure 28's identification family with prescribed transferred sheets for
the two Position II.a members. -/
noncomputable def figure28MembersWithExtra
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraFirst)
    (extraFirst_separate : ¬(data.edgePartition profile.first.1.1.1).Rel
      profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraSecond)
    (extraSecond_separate : ¬(data.edgePartition profile.second.1.1.1).Rel
      profile.second.1.1.2 extraSecond)
    (positionMember : WallMember data wall input.distinguishedBlock.1) :
    Fin 3 → WallMember data wall input.distinguishedBlock.1 :=
  ![positionMember,
    growMember ((growProfileFirst profile directions largest_index).withExtra
      extraFirst extraFirst_wall extraFirst_separate),
    growMember ((growProfileSecond profile directions largest_index).withExtra
      extraSecond extraSecond_wall extraSecond_separate)]

/-- Prescribing the transferred sheets does not change the three isolated
target directions. -/
theorem figure28MembersWithExtra_isolated
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraFirst)
    (extraFirst_separate : ¬(data.edgePartition profile.first.1.1.1).Rel
      profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      extraSecond)
    (extraSecond_separate : ¬(data.edgePartition profile.second.1.1.1).Rel
      profile.second.1.1.2 extraSecond)
    (positionMember : WallMember data wall input.distinguishedBlock.1)
    (hPosition : positionMember.isolated = profile.largest.1.1.1) :
    (figure28MembersWithExtra profile directions largest_index extraFirst
        extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
        extraSecond_separate positionMember 0).isolated = profile.largest.1.1.1 ∧
      (figure28MembersWithExtra profile directions largest_index extraFirst
        extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
        extraSecond_separate positionMember 1).isolated = profile.first.1.1.1 ∧
      (figure28MembersWithExtra profile directions largest_index extraFirst
        extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
        extraSecond_separate positionMember 2).isolated = profile.second.1.1.1 :=
  ⟨hPosition, rfl, rfl⟩

/-- The three isolated directions of the family: `t₄`, `t₂`, `t₃`. -/
theorem figure28Members_isolated
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (positionMember : WallMember data wall input.distinguishedBlock.1)
    (hPosition : positionMember.isolated = profile.largest.1.1.1) :
    (figure28Members profile directions largest_index positionMember 0).isolated =
        profile.largest.1.1.1 ∧
      (figure28Members profile directions largest_index positionMember 1).isolated =
        profile.first.1.1.1 ∧
      (figure28Members profile directions largest_index positionMember 2).isolated =
        profile.second.1.1.1 :=
  ⟨hPosition, rfl, rfl⟩

/-- **The three directions genuinely separate the family.**  `t₂ ≠ t₃` is the
classification payload's own `directions` field, and `t₂ ≠ t₄`, `t₃ ≠ t₄` are
the profile's `first_target_ne`, `second_target_ne`.  So the index the
identification names is not an artefact of the combinator's existential: the
incoming cover's isolated direction determines it. -/
theorem figure28Directions_injective
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (positionMember : WallMember data wall input.distinguishedBlock.1)
    (hPosition : positionMember.isolated = profile.largest.1.1.1)
    {first second : Fin 3}
    (hEq : (figure28Members profile directions largest_index positionMember first).isolated =
      (figure28Members profile directions largest_index positionMember second).isolated) :
    first = second := by
  obtain ⟨hZero, hOne', hTwo⟩ := figure28Members_isolated profile directions largest_index
    positionMember hPosition
  match first, second with
  | 0, 0 => rfl
  | 0, 1 => exact absurd ((hZero.symm.trans hEq).trans hOne').symm profile.first_target_ne
  | 0, 2 => exact absurd ((hZero.symm.trans hEq).trans hTwo).symm profile.second_target_ne
  | 1, 0 => exact absurd ((hOne'.symm.trans hEq).trans hZero) profile.first_target_ne
  | 1, 1 => rfl
  | 1, 2 => exact absurd ((hOne'.symm.trans hEq).trans hTwo) directions
  | 2, 0 => exact absurd ((hTwo.symm.trans hEq).trans hZero) profile.second_target_ne
  | 2, 1 => exact absurd ((hTwo.symm.trans hEq).trans hOne').symm directions
  | 2, 2 => rfl

/-- **The identification family exists**, on exactly the payload of
`W3IncomingClassification.Classification.four`.  Nothing beyond that payload is
needed: `W3FourIncomingCensus.exists_positionMember` supplies the `t₄` member
over the very datum the incoming cover lives on. -/
theorem exists_figure28Members
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ∃ positionMember : WallMember data wall input.distinguishedBlock.1,
      positionMember.isolated = profile.largest.1.1.1 :=
  exists_positionMember (ofGrowProfile (growProfileFirst profile directions largest_index))
    (W3FourSurvival.SelectedSurvival.ofGrowProfile
      (growProfileFirst profile directions largest_index))
    input.distinguishedBlock.1
    (growProfileFirst profile directions largest_index).growAnchor_wall_rel

end Family

/-! ## §3  The identification -/

section Identification

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
  (members : Fin 3 → WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
    input.distinguishedBlock.1)

include hForest

/-- **The identification step of the `w3Four` case.**

An incoming `w3Four` cover, presented against any family of Figure 28 members
over its own wall datum whose isolated directions exhaust the three survivors,
*is* one of them, together with the literal `Option` column dictionary and the
normalization receipt `W3Nd2IncomingMemberMatching.NormalizedAgainst`, whose
recorded clauses -- original target-edge labelling, unchanged length matrix,
occurrence-for-occurrence source map, preserved stable-row matrix entries --
forbid a hidden incoming classification or a count-based row bijection.

The exit is `IncomingMatchingCore.exists_member_normalization_of_family` at
`n = 3`, with the incoming isolated direction as `selector` and the members'
own isolated directions as `value`.  The dichotomy is
`W3FourIncomingCensus.divalentOccurrence_eq_grow_or_other_or_largest`, and
`figure28Directions_injective` records that the index it returns is unique.

Every member lives over the incoming cover's own wall datum
`contractDatum data hc hab hOne`, so no gauge copy, no `WallTransport` and no
branch swap occurs anywhere in this statement or its proof. -/
theorem exists_member_normalization
    (hDichotomy : ∃ index : Fin 3,
      divalentOccurrence data hc hab hOne fullDim star = (members index).isolated)
    (hCensus : ∀ index : Fin 3,
      divalentOccurrence data hc hab hOne fullDim star = (members index).isolated →
      SelectedCensus data hc hab hOne star input (members index).selectedLeft
        (members index).selectedRight (members index).selectedNew) :
    ∃ index : Fin 3,
      ∃ hIndex : divalentOccurrence data hc hab hOne fullDim star =
          (members index).isolated,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (W3FourIncomingCensus.memberTargetIso data hc hab hOne fullDim star
                  (members index) hIndex.symm)
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (members index).candidate.right column) ∧
          W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
            (W3FourIncomingCensus.memberTargetIso data hc hab hOne fullDim star
              (members index) hIndex.symm)
            (members index).candidate.datum
            (member_sameBlocks data hc hab hOne fullDim hForest star input (members index)
              hIndex.symm (hCensus index hIndex)).1
            (member_sameBlocks data hc hab hOne fullDim hForest star input (members index)
              hIndex.symm (hCensus index hIndex)).2 :=
  IncomingMatchingCore.exists_member_normalization_of_family data hc hab hOne
    fullDim.targetConnected fullDim.targetGenus (fun index ↦ (members index).candidate)
    (divalentOccurrence data hc hab hOne fullDim star)
    (fun index ↦ (members index).isolated) hDichotomy
    (fun index hIndex ↦ W3FourIncomingCensus.member_placement data hc hab hOne fullDim
      star (members index) hIndex.symm)
    (fun index hIndex ↦ W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
      (W3FourIncomingCensus.memberTargetIso data hc hab hOne fullDim star (members index)
        hIndex.symm)
      (members index).candidate.datum
      (member_sameBlocks data hc hab hOne fullDim hForest star input (members index)
        hIndex.symm (hCensus index hIndex)).1
      (member_sameBlocks data hc hab hOne fullDim hForest star input (members index)
        hIndex.symm (hCensus index hIndex)).2)
    (fun _ _ ↦ W3Nd2IncomingMemberMatching.normalizedAgainst data fullDim _ _ _ _)

include hCompat

/-- **The dichotomy the identification consumes, discharged from the `w3Four`
classification payload.**  With the family built by `figure28Members`, the
incoming cover's isolated direction is one of the three members' by
`W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest`. -/
theorem figure28Members_dichotomy
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1)
    (positionMember : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
      input.distinguishedBlock.1)
    (hPosition : positionMember.isolated = profile.largest.1.1.1) :
    ∃ index : Fin 3,
      divalentOccurrence data hc hab hOne fullDim star =
        (figure28Members profile directions largest_index positionMember index).isolated := by
  obtain ⟨hZero, hOne', hTwo⟩ := figure28Members_isolated profile directions largest_index
    positionMember hPosition
  rcases W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest data hc hab
      hOne fullDim hForest hCompat star input profile directions largest_index with
    hFirst | hSecond | hLargest
  · exact ⟨1, hFirst.trans hOne'.symm⟩
  · exact ⟨2, hSecond.trans hTwo.symm⟩
  · exact ⟨0, hLargest.trans hZero.symm⟩

/-- The same incoming-direction exhaustiveness for prescribed Position II.a
transferred sheets. -/
theorem figure28MembersWithExtra_dichotomy
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1)
    (extraFirst : Fin degree)
    (extraFirst_wall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      input.distinguishedBlock.1 extraFirst)
    (extraFirst_separate : ¬((contractDatum data hc hab hOne).edgePartition
      profile.first.1.1.1).Rel profile.first.1.1.2 extraFirst)
    (extraSecond : Fin degree)
    (extraSecond_wall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      input.distinguishedBlock.1 extraSecond)
    (extraSecond_separate : ¬((contractDatum data hc hab hOne).edgePartition
      profile.second.1.1.1).Rel profile.second.1.1.2 extraSecond)
    (positionMember : WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
      input.distinguishedBlock.1)
    (hPosition : positionMember.isolated = profile.largest.1.1.1) :
    ∃ index : Fin 3,
      divalentOccurrence data hc hab hOne fullDim star =
        (figure28MembersWithExtra profile directions largest_index extraFirst
          extraFirst_wall extraFirst_separate extraSecond extraSecond_wall
          extraSecond_separate positionMember index).isolated := by
  obtain ⟨hZero, hOne', hTwo⟩ := figure28MembersWithExtra_isolated profile directions
    largest_index extraFirst extraFirst_wall extraFirst_separate extraSecond
    extraSecond_wall extraSecond_separate positionMember hPosition
  rcases W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest data hc hab
      hOne fullDim hForest hCompat star input profile directions largest_index with
    hFirst | hSecond | hLargest
  · exact ⟨1, hFirst.trans hOne'.symm⟩
  · exact ⟨2, hSecond.trans hTwo.symm⟩
  · exact ⟨0, hLargest.trans hZero.symm⟩

end Identification

end DraismaVargas.LocalCases.W3FourIncomingMatching
