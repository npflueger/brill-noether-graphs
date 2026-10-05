module

public import DraismaVargas.LocalCases.W3ShiftIncomingCensus

@[expose] public section

/-!
# Matching an incoming `w3Shift` datum to a named Figure 29 member

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and
Equation (3).

This is the second of the two identification modules of the `w3Shift` case,
after `W3ShiftIncomingCensus`.  Given

* the incoming cover's own Figure 29 orientation
  (`W3ShiftIncomingCensus.exists_shiftProfile_movingTarget_eq_divalent`),
* the member-side block dictionary
  (`W3ShiftIncomingCensus.grow_*` / `shrink_*`), and
* the **selected block census** -- the three literal sheet classes the incoming
  cover displays at the two restored endpoints and at the contracted
  occurrence, taken here as a named hypothesis bundle `SelectedCensus` --

it produces the three wall comparisons, the pointwise `SameBlocks` families
against a named Figure 29 member, and the normalization receipt, through the
`n = 2` member-exit combinator
`IncomingMatchingCore.exists_member_normalization_of_family`.

## `IncomingMatchingCore.wall_blocks_of_dictionary` does not fit Figure 29

Item H of the core fixes the divalent endpoint's selected class:
its `hLeftSelected` slot reads

`(memberResolution C).left.block sheet = (mergedPartition data a b).block sheet`,

and its proof derives the incoming half of that position from `hURefines`
together with `hUJoined`, i.e. from the divalent original endpoint carrying the
**whole** distinguished wall class `A₀`.  That is true of Figure 30's `M⁽¹⁾` and
of Figure 31's members, and it is **false for both Figure 29 members**: Position
II.a puts `A' = e_α ∪ {x}` at the new divalent endpoint and Position II.b puts
`A' = e_α`, and `k_α < |A₀|` is the case hypothesis, so neither is `A₀`.

`wall_blocks_of_free_dictionary` below is the core's item H with **all three**
selected positions free, the incoming side of each supplied as a hypothesis
instead of two of them being derived from a join.  The proof is the core's, with
the `hURefines`/`hUJoined` branch replaced by one more `Eq.trans`.  The core's
item H is its special case
`selectedLeft = selectedRight = selectedNew = mergedPartition data a b` composed
with `wall_blocks_of_dictionary_of_joined`, and
`IncomingMatchingCore.block_eq_of_anchored_dictionary` generalizes both.

## What is a hypothesis here, and what discharges it

`SelectedCensus` is the exact analogue of
`W3Nd3IncomingCensus.selected_sheet_classes_of_shared` / `_of_largest` (and of
`W3Nd2IncomingSelectedCensus.selected_fibre_census`): the statement that the
incoming cover's own sheet classes over the distinguished wall block at the two
restored endpoints and at the contracted occurrence are the ones a named
Figure 29 position displays.  Discharging it needs the incoming pruned-fibre
census at a trivalent wall -- `W3Nd3IncomingCensus`'s `activeFibre_nonempty`,
`active_excess_sum`, `sideEnd_injOn`, `internalEdges_card_le_side_card`,
`otherSide_card_le_one` and the two `selected_fibre_census_*` -- and it is
**not** done here: `W3ShiftSelectedCensus` does it.  Nothing else in this module
is hypothesised: the direction census, the placement, the member dictionary,
the `r = 0` background census, the whole-cover exhaustion and the
normalization receipt are all proved here or consumed from other modules.

## The `r = 0` background is profile-free and is consumed verbatim

`W3Nd2IncomingMemberMatching.background_edge_block_eq_of_left_divalent`,
`background_trivalent_block_eq_of_left_divalent` and their two mirrors mention
no profile and no figure; they are exactly the two background inputs the free
dictionary needs, and they are applied unchanged.  Likewise
`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks` performs the
vertex/occurrence exhaustion for an arbitrary assembled candidate and an
arbitrary `Placement`, and `normalizedAgainst` supplies the receipt.

## The gauge copy does not enter

Everything below lives over the incoming cover's own wall datum
`contractDatum data hc hab hOne`.  See `W3ShiftIncomingCensus`'s header for why
an identification against a member over `W3ShiftClosure.exists_gauge_shift_pair`'s
copy `gaugeData` would be comparing the incoming cover's partitions with
partitions that the branch swap has moved, and `W3ShiftIncomingTransport` for
the transport that is then needed.

## Which member, and how the pair is separated

Both Figure 29 members carry the same side predicate, so -- unlike nd2 and nd3 --
the *placement* does not decide between them.  The selector of the combinator is
therefore the incoming cover's own class triple, and the two values are the two
members' displayed triples (`shiftClasses`).  `W3ShiftLimitRows.shiftMembers_ne`
is the numerical shadow of that separation: the dilation index of the regrown
occurrence through the residual sheet is `k_α − 1` for Position II.b and
`k_α + 1` for Position II.a, kept apart by the case's own `k_α ≥ 2`.
-/

namespace DraismaVargas.LocalCases.W3ShiftIncomingMatching

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion ResolutionM11 ResolutionCoarseFine
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_spec
  endpoint_valencies)
open W3ShiftSourceCandidates
open W3ShiftIncomingCensus

/-! ## The contracted wall partition is the merged partition -/

section Merged

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The contracted datum's wall partition is literally the merged partition.
Restated here, rather than imported from `W3Nd3IncomingMatching`, so that this
module does not acquire the nd3 matching chain. -/
theorem merged_eq_wall :
    mergedPartition data a b =
      (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ :=
  (contractDatum_vertexPartition_merge data hc hab hOne).symm

theorem merged_block_eq_wall_block (sheet : Fin degree) :
    (mergedPartition data a b).block sheet =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet :=
  congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
    (merged_eq_wall data hc hab hOne)

theorem merged_rel_iff_wall_rel (root sheet : Fin degree) :
    (mergedPartition data a b).Rel root sheet ↔
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel root sheet := by
  rw [merged_eq_wall data hc hab hOne]

end Merged

/-! ## The core's item H with all three selected positions free -/

section FreeDictionary

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **The three wall comparisons of one member, from a block dictionary with
every position free.**

This is `IncomingMatchingCore.wall_blocks_of_dictionary` with its fixed
`hLeftSelected` target `mergedPartition data a b` replaced by a free partition
`selectedLeft` and the matching incoming fact `hUSelected` taken as a
hypothesis, instead of being derived from `hURefines` and `hUJoined`.  The other
two positions were already free there.

Figure 29 needs this shape because neither of its members carries the whole
distinguished wall class at the new divalent endpoint: Position II.a carries
`e_α ∪ {x}` and Position II.b carries `e_α`, both of cardinality below `|A₀|`
by the case hypothesis `k_α < |A₀|`.

`u` is the original endpoint at which the flag occurrence and the contracted
occurrence both sit -- the divalent one -- and `v` is the other.  The six
member-side facts are exactly the dictionary
`W3ShiftIncomingCensus.grow_*`/`shrink_*` supplies. -/
theorem wall_blocks_of_free_dictionary
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (root : Fin degree) (u v : target.V) (flag : target.edges)
    (flagPartition selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hFlagEq : ∀ sheet, (data.edgePartition flag).block sheet = flagPartition.block sheet)
    (hFlagAt : flag ∈ GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hUSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition u).block sheet = selectedLeft.block sheet)
    (hVSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = selectedRight.block sheet)
    (hNewSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.edgePartition contracted).block sheet = selectedNew.block sheet)
    (hLeftSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet = selectedLeft.block sheet)
    (hRightSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet = selectedRight.block sheet)
    (hNewMember : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet = selectedNew.block sheet)
    (hLeftBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet = flagPartition.block sheet)
    (hRightBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet =
        (mergedPartition data a b).block sheet)
    (hNewBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet =
        flagPartition.block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (W3Nd2IncomingMemberMatching.pasted C).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (W3Nd2IncomingMemberMatching.pasted C).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hUSelected sheet hSel).trans (hLeftSelected sheet hSel).symm
    · exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet)).trans
        (hLeftBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hVSelected sheet hSel).trans (hRightSelected sheet hSel).symm
    · exact (hBgTri sheet hSel).trans (hRightBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hNewSelected sheet hSel).trans (hNewMember sheet hSel).symm
    · exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet))).trans
        (hNewBackground sheet hSel).symm

end FreeDictionary

/-! ## The selected block census, as a named hypothesis bundle -/

section Census

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

/-- **The incoming cover's own sheet classes over the distinguished wall
block**, at the divalent original endpoint, at the trivalent one and at the
contracted occurrence, in the orientation-free form the matching step consumes.

This is the exact analogue of `W3Nd3IncomingCensus.selected_sheet_classes_of_shared`
/ `_of_largest` and of `W3Nd2IncomingSelectedCensus.selected_fibre_census`, and
it is the one thing `W3ShiftIncomingMatching` hypothesises.  Discharging it
needs the incoming pruned-fibre census at a trivalent wall; see this module's
header.

The two fields are the two branches of
`W3Nd2IncomingTargetPlacement.endpoint_valencies`: in each, the first component
is the **divalent** original endpoint, which is the one the member's `left` end
restores (`W3Nd2IncomingMemberMatching.transported_endpoints_of_left_divalent`
and its mirror). -/
structure SelectedCensus (selectedLeft selectedRight selectedNew : SheetPartition degree) :
    Prop where
  /-- `a` divalent: `a` carries `selectedLeft`, `b` carries `selectedRight`. -/
  divalentLeft : (GluingDatum.incidentEdges a).card = 2 →
    (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition a).block sheet = selectedLeft.block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition b).block sheet = selectedRight.block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.edgePartition contracted).block sheet = selectedNew.block sheet)
  /-- `b` divalent: the mirror. -/
  divalentRight : (GluingDatum.incidentEdges b).card = 2 →
    (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition b).block sheet = selectedLeft.block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition a).block sheet = selectedRight.block sheet) ∧
      (∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.edgePartition contracted).block sheet = selectedNew.block sheet)

/-- The distinguished block's merged relation, read at the moving anchor. -/
theorem merged_rel_iff_movingAnchor (shift : ShiftProfile input) (sheet : Fin degree) :
    (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet ↔
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        shift.movingAnchor sheet := by
  rw [merged_rel_iff_wall_rel data hc hab hOne]
  exact ⟨fun h ↦ shift.movingAnchor_wall_rel.symm.trans h,
    fun h ↦ shift.movingAnchor_wall_rel.trans h⟩

end Census

/-! ## The pointwise match against one Figure 29 member -/

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

/-- **An incoming `w3Shift` cover matches a Figure 29 member, pointwise.**

Stated for an arbitrary assembled candidate over the incoming wall datum whose
side predicate isolates the moving direction and whose pasted wall partitions
are described by the six-fact dictionary; Figure 29's shrink and grow members
are the two instances.  The three wall comparisons come from
`wall_blocks_of_free_dictionary`, the vertex/occurrence exhaustion from
`W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks`, and the `r = 0`
background from the profile-free `W3Nd2IncomingMemberMatching.background_*`
family. -/
theorem shift_sameBlocks
    (shift : ShiftProfile input)
    (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hSide : ∀ edge, C.right edge = rightOf shift.movingTarget edge)
    (hPlacement : IncomingMatchingCore.Placement hc hab hOne C.right)
    (selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft selectedRight
      selectedNew)
    (hLeftSelected : ∀ sheet,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet = selectedLeft.block sheet)
    (hRightSelected : ∀ sheet,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet = selectedRight.block sheet)
    (hNewMember : ∀ sheet,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet = selectedNew.block sheet)
    (hLeftBackground : ∀ sheet,
      ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet =
        ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block sheet)
    (hRightBackground : ∀ sheet,
      ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet =
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet)
    (hNewBackground : ∀ sheet,
      ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          shift.movingAnchor sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet =
        ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block sheet) :
    (∀ vertex, ((GluingTransport.transport
          (W3ShiftIncomingCensus.shiftTargetIso data hc hab hOne C hPlacement)
          data).vertexPartition vertex).SameBlocks (C.datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (W3ShiftIncomingCensus.shiftTargetIso data hc hab hOne C hPlacement)
          data).edgePartition edge).SameBlocks (C.datum.edgePartition edge)) := by
  classical
  have hSideDiv : ∀ edge, C.right edge =
      rightOf (divalentOccurrence data hc hab hOne fullDim star) edge := fun edge ↦
    (hSide edge).trans (congrArg (fun place ↦ rightOf place edge) hMoving)
  have hFlagEq : ∀ sheet, (data.edgePartition (unfoldEdge hc hab hOne
        (divalentOccurrence data hc hab hOne fullDim star))).block sheet =
      ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block sheet := by
    intro sheet
    rw [hMoving, contractDatum_edgePartition]
  have hMerged : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet ↔
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        shift.movingAnchor sheet :=
    merged_rel_iff_movingAnchor data hc hab hOne star input shift
  have hLeftSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet = selectedLeft.block sheet :=
    fun sheet h ↦ hLeftSelected sheet ((hMerged sheet).mp h)
  have hRightSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet = selectedRight.block sheet :=
    fun sheet h ↦ hRightSelected sheet ((hMerged sheet).mp h)
  have hNewSel' : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet = selectedNew.block sheet :=
    fun sheet h ↦ hNewMember sheet ((hMerged sheet).mp h)
  have hLeftBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).left.block sheet =
        ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block sheet :=
    fun sheet h ↦ hLeftBackground sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
  have hRightBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).right.block sheet =
        (mergedPartition data a b).block sheet := by
    intro sheet h
    rw [merged_block_eq_wall_block data hc hab hOne sheet]
    exact hRightBackground sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
  have hNewBg' : ∀ sheet, ¬ (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (W3Nd2IncomingMemberMatching.pasted C).newEdge.block sheet =
        ((contractDatum data hc hab hOne).edgePartition shift.movingTarget).block sheet :=
    fun sheet h ↦ hNewBackground sheet (fun hRel ↦ h ((hMerged sheet).mpr hRel))
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
      wall_blocks_of_free_dictionary data hc hab hOne C input.distinguishedBlock.1 a b _
        _ selectedLeft selectedRight selectedNew hFlagEq hFlagAt
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
        fullDim star C.right hPlacement hSideDiv hLeftDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus C hPlacement
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
      wall_blocks_of_free_dictionary data hc hab hOne C input.distinguishedBlock.1 b a _
        _ selectedLeft selectedRight selectedNew hFlagEq hFlagAt
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
        fullDim star C.right hPlacement hSideDiv hRightDiv
    exact W3Nd2IncomingMemberMatching.sameBlocks_of_wall_blocks data hc hab hOne
      fullDim.targetConnected fullDim.targetGenus C hPlacement
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransLeft).trans (hBlockLeft sheet))
      (fun sheet ↦ (congrArg (fun partition : SheetPartition degree ↦ partition.block sheet)
        hTransRight).trans (hBlockRight sheet))
      hBlockNew

end Matching

/-! ## Figure 29's pair, as the two values of one selector -/

section Classes

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- **The class triples Figure 29's two members display on the distinguished
wall block**: the divalent endpoint's class, the trivalent endpoint's class and
the new edge's class, in the order
`W3ShiftLimitRows.shiftMembers` lists the members -- Position II.b
(`A' = e_α`, `A⁽ᵠ⁾ = A₀ ∖ {x}`, `e' = e_α ∖ {x}`, index `k_α − 1`) first, then
Position II.a (`A' = e_α ∪ {x}`, `A₀`, `e' = e_α ∪ {x}`, index `k_α + 1`).

These triples are the combinator's `value`; the incoming cover's own triple is
its `selector`.  Unlike nd2 and nd3, the two members' side predicates are equal
(`W3ShiftIncomingCensus.growCandidate_right`, `shrinkCandidate_right`), so the
placement cannot be the selector and this triple is what separates the pair.
`W3ShiftLimitRows.shiftMembers_ne` is the same separation read numerically. -/
noncomputable def shiftClasses {shift : ShiftProfile input} (shrink : ShrinkData shift) :
    Fin 2 → SheetPartition degree × SheetPartition degree × SheetPartition degree :=
  ![(data.edgePartition shift.movingTarget,
      (data.vertexPartition wall).detachSheet shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_wall_rel,
      (data.edgePartition shift.movingTarget).detachSheet shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_moving),
    (shift.growPartition, data.vertexPartition wall, shift.growPartition)]

/-- Both members isolate the moving direction. -/
theorem shiftMembers_right {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (index : Fin 2) (edge : target.edges) :
    (W3ShiftLimitRows.shiftMembers shrink index).right edge =
      rightOf shift.movingTarget edge := by
  match index with
  | 0 => exact W3ShiftIncomingCensus.shrinkCandidate_right shrink edge
  | 1 => exact W3ShiftIncomingCensus.growCandidate_right shift edge

/-- The selected half of the member dictionary, for both members at once. -/
theorem shiftMembers_pasted_selected {shift : ShiftProfile input}
    (shrink : ShrinkData shift) (index : Fin 2) (sheet : Fin degree)
    (hSel : (data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).left.block sheet =
        (shiftClasses shrink index).1.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).right.block sheet =
        (shiftClasses shrink index).2.1.block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).newEdge.block sheet =
        (shiftClasses shrink index).2.2.block sheet := by
  match index with
  | 0 => exact ⟨W3ShiftIncomingCensus.shrink_left_selected shrink sheet hSel,
      W3ShiftIncomingCensus.shrink_right_selected shrink sheet hSel,
      W3ShiftIncomingCensus.shrink_newEdge_selected shrink sheet hSel⟩
  | 1 => exact ⟨W3ShiftIncomingCensus.grow_left_selected shift sheet hSel,
      W3ShiftIncomingCensus.grow_right_selected shift sheet hSel,
      W3ShiftIncomingCensus.grow_newEdge_selected shift sheet hSel⟩

/-- The background half: both members are assembled on the one background
`W3ShiftSourceCandidates.ShiftProfile.background`, so the three off-block
partitions are `e_α`, `A₀`, `e_α` for each. -/
theorem shiftMembers_pasted_background {shift : ShiftProfile input}
    (shrink : ShrinkData shift) (index : Fin 2) (sheet : Fin degree)
    (hOff : ¬(data.vertexPartition wall).Rel shift.movingAnchor sheet) :
    (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).left.block sheet =
        (data.edgePartition shift.movingTarget).block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).right.block sheet =
        (data.vertexPartition wall).block sheet ∧
      (W3Nd2IncomingMemberMatching.pasted
        (W3ShiftLimitRows.shiftMembers shrink index)).newEdge.block sheet =
        (data.edgePartition shift.movingTarget).block sheet := by
  match index with
  | 0 => exact ⟨W3ShiftIncomingCensus.shrink_left_background shrink sheet hOff,
      W3ShiftIncomingCensus.shrink_right_background shrink sheet hOff,
      W3ShiftIncomingCensus.shrink_newEdge_background shrink sheet hOff⟩
  | 1 => exact ⟨W3ShiftIncomingCensus.grow_left_background shift sheet hOff,
      W3ShiftIncomingCensus.grow_right_background shift sheet hOff,
      W3ShiftIncomingCensus.grow_newEdge_background shift sheet hOff⟩


/-- **The selector genuinely separates Figure 29's pair.**  Read at the residual
sheet `remainder`, Position II.b's new-edge class has `k_α − 1` sheets and
Position II.a's has `k_α + 1`, and the case's own `2 ≤ k_α`
(`W3ShiftSourceCandidates.ShiftProfile.two_le_moving`) keeps them apart.  This is
`W3ShiftLimitRows.shiftMembers_ne`'s observable, read on the class triples the
combinator selects by rather than on the assembled members. -/
theorem shiftClasses_ne {shift : ShiftProfile input} (shrink : ShrinkData shift) :
    shiftClasses shrink 0 ≠ shiftClasses shrink 1 := by
  intro hEq
  have hNew : ((data.edgePartition shift.movingTarget).detachSheet shrink.transfer
      shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving) =
      shift.growPartition := congrArg (fun triple ↦ triple.2.2) hEq
  have hShrink : shrink.selected.newEdge.blockCard shrink.remainder + 1 =
      data.sourceEdgeIndex shift.moving.1 := shrink.newEdge_blockCard_remainder
  have hMovingRel : (data.edgePartition shift.movingTarget).Rel shift.movingAnchor
      shrink.remainder := shrink.transfer_moving.trans shrink.remainder_moving
  have hGrowRel : shift.growPartition.Rel shift.movingAnchor shrink.remainder :=
    (shift.growPartition_rel_movingAnchor_iff shrink.remainder).mpr (Or.inl hMovingRel)
  have hGrow : shift.growPartition.blockCard shrink.remainder =
      data.sourceEdgeIndex shift.moving.1 + 1 := by
    rw [← SheetPartition.blockCard_congr shift.growPartition hGrowRel]
    exact shift.growPartition_blockCard_movingAnchor
  rw [show shrink.selected.newEdge = (data.edgePartition shift.movingTarget).detachSheet
      shrink.transfer shrink.remainder shrink.transfer_ne_remainder
      shrink.remainder_moving from rfl, hNew, hGrow] at hShrink
  omega

/-- Consequently the combinator's index is determined by the incoming cover's
class triple. -/
theorem shiftClasses_injective {shift : ShiftProfile input} (shrink : ShrinkData shift)
    {first second : Fin 2}
    (hEq : shiftClasses shrink first = shiftClasses shrink second) : first = second := by
  match first, second with
  | 0, 0 => rfl
  | 0, 1 => exact absurd hEq (shiftClasses_ne shrink)
  | 1, 0 => exact absurd hEq.symm (shiftClasses_ne shrink)
  | 1, 1 => rfl

/-- **The Figure 29 position the identification names is unique.**  So
`exists_member_normalization`'s `index` is not an artefact of the combinator's
existential: the incoming cover's class triple determines it. -/
theorem identified_index_unique {shift : ShiftProfile input} (shrink : ShrinkData shift)
    (triple : SheetPartition degree × SheetPartition degree × SheetPartition degree)
    {first second : Fin 2} (hFirst : triple = shiftClasses shrink first)
    (hSecond : triple = shiftClasses shrink second) : first = second :=
  shiftClasses_injective shrink (hFirst.symm.trans hSecond)

/-- The same separation at the level of the assembled members, which is
`W3ShiftLimitRows.shiftMembers_ne` itself. -/
theorem shiftMembers_ne_of_ne {shift : ShiftProfile input} (shrink : ShrinkData shift)
    {first second : Fin 2} (hNe : first ≠ second) :
    W3ShiftLimitRows.shiftMembers shrink first ≠
      W3ShiftLimitRows.shiftMembers shrink second := by
  match first, second with
  | 0, 0 => exact absurd rfl hNe
  | 0, 1 => exact W3ShiftLimitRows.shiftMembers_ne shrink
  | 1, 0 => exact fun hEq ↦ W3ShiftLimitRows.shiftMembers_ne shrink hEq.symm
  | 1, 1 => exact absurd rfl hNe

end Classes

/-! ## The identification -/

section Identification

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (shift : ShiftProfile input)
  (hMoving : shift.movingTarget = divalentOccurrence data hc hab hOne fullDim star)
  (shrink : ShrinkData shift)
  (selectedLeft selectedRight selectedNew : SheetPartition degree)

include fullDim hMoving

/-- The placement of either Figure 29 member. -/
theorem shiftMembers_placement (index : Fin 2) :
    IncomingMatchingCore.Placement hc hab hOne
      (W3ShiftLimitRows.shiftMembers shrink index).right :=
  W3ShiftIncomingCensus.placement_of_movingTarget_eq data hc hab hOne fullDim star _
    (fun edge ↦ (shiftMembers_right shrink index edge).trans
      (congrArg (fun place ↦ rightOf place edge) hMoving))

include hForest

/-- The pointwise match against the member named by a class triple. -/
theorem shiftMembers_sameBlocks
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft selectedRight
      selectedNew)
    (index : Fin 2)
    (hIndex : (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index) :
    (∀ vertex, ((GluingTransport.transport
          (IncomingMatchingCore.memberTargetIso data hc hab hOne
            (W3ShiftLimitRows.shiftMembers shrink index)
            (shiftMembers_placement data hc hab hOne fullDim star input shift hMoving
              shrink index))
          data).vertexPartition vertex).SameBlocks
        ((W3ShiftLimitRows.shiftMembers shrink index).datum.vertexPartition vertex)) ∧
      (∀ edge, ((GluingTransport.transport
          (IncomingMatchingCore.memberTargetIso data hc hab hOne
            (W3ShiftLimitRows.shiftMembers shrink index)
            (shiftMembers_placement data hc hab hOne fullDim star input shift hMoving
              shrink index))
          data).edgePartition edge).SameBlocks
        ((W3ShiftLimitRows.shiftMembers shrink index).datum.edgePartition edge)) := by
  have hLeft : selectedLeft = (shiftClasses shrink index).1 := congrArg Prod.fst hIndex
  have hRight : selectedRight = (shiftClasses shrink index).2.1 :=
    congrArg (fun triple ↦ triple.2.1) hIndex
  have hNew : selectedNew = (shiftClasses shrink index).2.2 :=
    congrArg (fun triple ↦ triple.2.2) hIndex
  refine shift_sameBlocks data hc hab hOne fullDim hForest star input shift hMoving
    (W3ShiftLimitRows.shiftMembers shrink index) (shiftMembers_right shrink index) _
    selectedLeft selectedRight selectedNew hCensus ?_ ?_ ?_ ?_ ?_ ?_
  · intro sheet hSel
    rw [hLeft]
    exact (shiftMembers_pasted_selected shrink index sheet hSel).1
  · intro sheet hSel
    rw [hRight]
    exact (shiftMembers_pasted_selected shrink index sheet hSel).2.1
  · intro sheet hSel
    rw [hNew]
    exact (shiftMembers_pasted_selected shrink index sheet hSel).2.2
  · intro sheet hOff
    exact (shiftMembers_pasted_background shrink index sheet hOff).1
  · intro sheet hOff
    exact (shiftMembers_pasted_background shrink index sheet hOff).2.1
  · intro sheet hOff
    exact (shiftMembers_pasted_background shrink index sheet hOff).2.2

/-- **The identification step.**  An incoming `w3Shift` cover whose isolated
target direction is the moving one and whose selected-block classes are those of
a named Figure 29 position *is* that member of Equation (3)'s pair, together
with the literal `Option` column dictionary and the normalization receipt
`W3Nd2IncomingMemberMatching.NormalizedAgainst`, whose recorded clauses --
original target-edge labelling, unchanged length matrix, occurrence-for-occurrence
source map, preserved stable-row matrix entries -- forbid a hidden incoming
classification or a count-based row bijection.

The exit is `IncomingMatchingCore.exists_member_normalization_of_family` at
`n = 2`, with the incoming class triple as `selector` and `shiftClasses` as
`value`.  `W3ShiftLimitRows.shiftMembers_ne` records that the two values are
genuinely distinct members: `k_α − 1` against `k_α + 1` at one and the same
sheet.

Both members live over the incoming cover's own wall datum
`contractDatum data hc hab hOne`, so no gauge copy and no `WallTransport` occurs
anywhere in this statement or its proof.  When no `ShrinkData` exists over
that datum, the transport of `W3ShiftIncomingTransport` is needed. -/
theorem exists_member_normalization
    (hCensus : SelectedCensus data hc hab hOne star input selectedLeft selectedRight
      selectedNew)
    (hDichotomy : ∃ index : Fin 2,
      (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index) :
    ∃ index : Fin 2,
      ∃ hIndex : (selectedLeft, selectedRight, selectedNew) = shiftClasses shrink index,
        (∀ column : Option (contract target hab hOne).edges,
            GluingTransport.edgeEquiv
                (IncomingMatchingCore.memberTargetIso data hc hab hOne
                  (W3ShiftLimitRows.shiftMembers shrink index)
                  (shiftMembers_placement data hc hab hOne fullDim star input shift
                    hMoving shrink index))
                (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
              TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (W3ShiftLimitRows.shiftMembers shrink index).right column) ∧
          W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
            (IncomingMatchingCore.memberTargetIso data hc hab hOne
              (W3ShiftLimitRows.shiftMembers shrink index)
              (shiftMembers_placement data hc hab hOne fullDim star input shift hMoving
                shrink index))
            (W3ShiftLimitRows.shiftMembers shrink index).datum
            (shiftMembers_sameBlocks data hc hab hOne fullDim hForest star input shift
              hMoving shrink selectedLeft selectedRight selectedNew hCensus index
              hIndex).1
            (shiftMembers_sameBlocks data hc hab hOne fullDim hForest star input shift
              hMoving shrink selectedLeft selectedRight selectedNew hCensus index
              hIndex).2 :=
  IncomingMatchingCore.exists_member_normalization_of_family data hc hab hOne
    fullDim.targetConnected fullDim.targetGenus
    (W3ShiftLimitRows.shiftMembers shrink)
    (selectedLeft, selectedRight, selectedNew) (shiftClasses shrink) hDichotomy
    (fun index _ ↦ shiftMembers_placement data hc hab hOne fullDim star input shift
      hMoving shrink index)
    (fun index hIndex ↦ W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
      (IncomingMatchingCore.memberTargetIso data hc hab hOne
        (W3ShiftLimitRows.shiftMembers shrink index)
        (shiftMembers_placement data hc hab hOne fullDim star input shift hMoving
          shrink index))
      (W3ShiftLimitRows.shiftMembers shrink index).datum
      (shiftMembers_sameBlocks data hc hab hOne fullDim hForest star input shift hMoving
        shrink selectedLeft selectedRight selectedNew hCensus index hIndex).1
      (shiftMembers_sameBlocks data hc hab hOne fullDim hForest star input shift hMoving
        shrink selectedLeft selectedRight selectedNew hCensus index hIndex).2)
    (fun _ _ ↦ W3Nd2IncomingMemberMatching.normalizedAgainst data fullDim _ _ _ _)

end Identification

end DraismaVargas.LocalCases.W3ShiftIncomingMatching
